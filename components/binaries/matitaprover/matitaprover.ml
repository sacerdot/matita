(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department, University of Bologna, Italy.                     
    ||I||                                                                
    ||T||  HELM is free software; you can redistribute it and/or         
    ||A||  modify it under the terms of the GNU General Public License   
    \   /  version 2 or (at your option) any later version.      
     \ /   This software is distributed as is, NO WARRANTY.     
      V_______________________________________________________________ *)

(* $Id: orderings.ml 9869 2009-06-11 22:52:38Z denes $ *)

module OT = struct type t = string  let compare = Pervasives.compare end 
module HC = Map.Make(OT)
module TS = HTopoSort.Make(OT)

type leaf = int * string

let cache = ref HC.empty 
let num = ref 100

let hash s = 
  try HC.find s !cache
  with Not_found ->
          cache := HC.add s (!num,s) !cache;
          decr num;
          HC.find s !cache
;;

hash "==";;
hash "_";;

let problem_file = ref "no-file-given";;
let tptppath = ref "/";;
let seconds = ref 0;;

let fail_msg () =
      print_endline ("% SZS status Timeout for " ^ 
        Filename.basename !problem_file)
;;
  
module type LeafComparer =
  sig
    val cmp : leaf -> leaf -> int
  end
;;

module MakeBlob(C:LeafComparer) : Terms.Blob 
  with type t = leaf and type input = Ast.term = struct
        type t = leaf
        let eq a b = a == b
        let compare a b = C.cmp a b
        let eqP = hash "=="
        let pp (_,a) =  a 
        type input = Ast.term
        let rec embed m = function
            | Ast.Variable name ->
                (try m, List.assoc name m
                 with Not_found -> 
                    let t = Terms.Var ~-(List.length m) in
                    (name,t)::m, t)
            | Ast.Constant name -> m, Terms.Leaf (hash name)
            | Ast.Function (name,args) -> 
                let m, args = 
                  HExtlib.list_mapi_acc 
                    (fun x _ m -> embed m x) m args
                in
                m, Terms.Node (Terms.Leaf (hash name):: args) 
        let is_eq = function
	  | Terms.Node [ Terms.Leaf eqt ; ty; l; r ] when eq eqP eqt ->
              Some (ty,l,r) 
	  | _ -> None
        let saturate bo ty = 
          let vars, ty = embed [] ty in
          let _, bo = embed vars bo in
          let bo = Terms.Node (bo :: List.map snd (List.rev vars)) in
          bo, ty
        ;;
        let embed t = snd(embed [] t);;

  end
;;

let success_msg bag l (pp : ?margin:int -> leaf Terms.unit_clause -> string) ord =
  (* TODO: do some sort of poor man lock (open + OEXCL) so that
   *       just one thread at a time prints the proof *)
  print_endline ("% SZS status Unsatisfiable for " ^ 
    Filename.basename !problem_file);
  print_endline ("% SZS output start CNFRefutation for " ^ 
    Filename.basename !problem_file);
  flush stdout;
  List.iter (fun x ->
    let (cl,_,_) = Terms.get_from_bag x bag in
    print_endline (pp ~margin:max_int 
      cl)) l;
  print_endline ("% SZS output end CNFRefutation for " ^ 
    Filename.basename !problem_file);
  let prefix = string_of_int (Unix.getpid ()) in
  let prerr_endline s = prerr_endline (prefix ^ ": " ^ s) in
  let times = Unix.times () in
  prerr_endline ("solved " ^ !problem_file ^ " in " ^ string_of_float
    (times.Unix.tms_utime +. times.Unix.tms_stime) ^ "(Process Time) using " ^ ord);
;;

let start_msg stats passives g_passives (pp : ?margin:int -> leaf Terms.unit_clause -> string) oname =
  let prefix = string_of_int (Unix.getpid ()) in
  let prerr_endline s = prerr_endline (prefix ^ ": " ^ s) in
  prerr_endline "Facts:";
  List.iter (fun x -> prerr_endline (" " ^ pp x)) passives;
  prerr_endline "Goal:";
  prerr_endline (" " ^ pp g_passives);
(*  prerr_endline "Order:";
  prerr_endline ("  " ^ oname);
  prerr_endline "Leaf order:";
  List.iter (fun ((_,name), (a,b,c,gp,l)) ->
     prerr_endline (" " ^name ^ " " ^ string_of_int a ^ " " ^
       string_of_int b ^ " " ^
       string_of_int c ^ " " ^
       String.concat "," (List.map string_of_int gp) ^ 
       String.concat "," (List.map snd l))) stats;*)
;;

let report_error s =  prerr_endline (string_of_int (Unix.getpid())^": "^s);;


module Main(P : Paramod.Paramod with type t = leaf) = struct

  (*let mk_clause bag maxvar (t,ty) =
    let (proof,ty) = B.saturate t ty in
    let c, maxvar = Utils.mk_unit_clause maxvar ty proof in
    let bag, c = Terms.add_to_bag c bag in
      (bag, maxvar), c
  ;;
  
  let mk_passive (bag,maxvar) = mk_clause bag maxvar;;
  let mk_goal (bag,maxvar) = mk_clause bag maxvar;;*)

 let run ~useage ~printmsg stats goal hypotheses pp_unit_clause name = 
   let bag = Terms.empty_bag, 0 in
   let bag, g_passives = P.mk_goal bag goal in
   let bag, passives = 
     HExtlib.list_mapi_acc (fun x _ b -> P.mk_passive b x) bag hypotheses 
   in
   if printmsg then start_msg stats passives g_passives pp_unit_clause name;
   match
     P.paramod ~useage
      ~max_steps:max_int bag ~g_passives:[g_passives] ~passives 
   with
   | P.Error s -> report_error s; 3
   | P.Unsatisfiable ((bag,_,_,l)::_) -> 
         success_msg bag l pp_unit_clause name; 0
   | P.Unsatisfiable ([]) -> 
         report_error "Unsatisfiable but no solution output"; 3
   | P.GaveUp -> 2
   | P.Timeout _ -> 1
 ;;
end

 let compute_stats goal hypotheses =
   let module C = 
     struct type t = leaf let cmp (a,_) (b,_) = Pervasives.compare a b end 
   in
   let module B = MakeBlob(C) in
   let module Pp = Pp.Pp(B) in
   let module O = Orderings.NRKBO(B) in
   let module P = Paramod.Paramod(O) in
   let module Stats = Stats.Stats(O) in
   let bag = Terms.empty_bag, 0 in
   let bag, g_passives = P.mk_goal bag goal in
   let bag, passives = 
     HExtlib.list_mapi_acc (fun x _ b -> P.mk_passive b x) bag hypotheses 
   in
   let data = Stats.parse_symbols passives g_passives in
   let data = 
     List.map
       (fun (name, n_occ, arity, n_gocc, g_pos) ->
          name, (n_occ, arity, n_gocc, g_pos, Stats.dependencies name passives))
       data
   in
   let oplist = List.map (fun ((_,x),_) -> x) data in
   let deps op = 
     (let _,(_,_,_,_,d) = List.find (fun ((_,op'),_) -> op = op') data 
      in List.map snd d)
   in 
   let oplist = TS.topological_sort oplist deps in
   List.sort 
     (fun ((_,n1),(o1,a1,go1,p1,_)) ((_,n2),(o2,a2,go2,p2,_)) ->
        if a1 = 0 && a2 = 0 then 0
        else if a1 = 0 then -1
        else if a2 = 0 then 1
        else let res = Pervasives.compare (a1,o1,-go1,p1) (a2,o2,-go2,p2)
             in if res = 0 then Pervasives.compare (HExtlib.list_index ((=) n1) oplist) (HExtlib.list_index ((=) n2) oplist)
                else res)
     data
 ;;

let worker order ~useage ~printmsg goal hypotheses =
   let stats = compute_stats goal hypotheses in
   let module C = 
     struct
      let cmp =
        let raw = List.map snd stats in
        let rec pos x = function
          | ((y,_)::tl) when y = x -> 0
          | _::tl -> 1 + pos x tl
          | [] -> assert false
        in
        if List.length raw = 
           List.length (HExtlib.list_uniq raw)
        then
          ((*prerr_endline "NO CLASH, using fixed ground order";*)
           fun a b ->
            Pervasives.compare 
              (pos a stats)
              (pos b stats))
        else
          ((*prerr_endline "CLASH, statistics insufficient";*)
            fun (a,_) (b,_) -> Pervasives.compare a b)
      ;;
     end
   in
   let module B = MakeBlob(C) in
   let module Pp = Pp.Pp(B) in
   match order with
   | `NRKBO ->
       let module O = Orderings.NRKBO(B) in
       let module Main = Main(Paramod.Paramod(O)) in
       Main.run ~useage ~printmsg stats goal hypotheses Pp.pp_unit_clause O.name
   | `KBO ->
       let module O = Orderings.KBO(B) in
       let module Main = Main(Paramod.Paramod(O)) in
       Main.run ~useage ~printmsg stats goal hypotheses Pp.pp_unit_clause O.name
   | `LPO ->
       let module O = Orderings.LPO(B) in
       let module Main = Main(Paramod.Paramod(O)) in
       Main.run ~useage ~printmsg stats goal hypotheses Pp.pp_unit_clause O.name
;;

let print_status p = 
  let print_endline s = () in (* prerr_endline (string_of_int p ^ ": " ^ s) in*)
    function
    | Unix.WEXITED 0 -> 
        print_endline ("status Unsatisfiable for " ^ 
          Filename.basename !problem_file);
    | Unix.WEXITED 1 -> 
        print_endline ("status Timeout for " ^ 
          Filename.basename !problem_file);
    | Unix.WEXITED 2 -> 
        print_endline ("status GaveUp for " ^ 
          Filename.basename !problem_file);
    | Unix.WEXITED 3 ->
        print_endline ("status Error for " ^ 
          Filename.basename !problem_file);
    | Unix.WEXITED _ -> assert false
    | Unix.WSIGNALED s -> print_endline ("killed by signal " ^ string_of_int s)
    | Unix.WSTOPPED _ -> print_endline "stopped"
 ;;

let killall l = 
  List.iter (fun pid -> try Unix.kill pid 9 with _ -> ()) l
;;

let main () =
  let childs = ref [] in
  let _ =
    Sys.signal 24 (Sys.Signal_handle 
      (fun _ -> fail_msg (); killall !childs; exit 1)) 
  in
  let _ =
    Sys.signal Sys.sigalrm 
      (Sys.Signal_handle (fun _ -> prerr_endline "Alarm!"; fail_msg (); killall !childs; exit 1)) 
  in
  Arg.parse [
   "--tptppath", Arg.String (fun p -> tptppath := p), 
     ("[path]  TPTP lib root, default " ^ !tptppath);
   "--timeout", Arg.Int (fun p -> seconds := p), 
     ("[seconds]  timeout, default none");
   ] (fun x -> problem_file := x) "
Matitaprover is the first order automatic prover that equips the 
Matita interactive theorem prover (http://matita.cs.unibo.it).

Developed by A.Asperti, M.Denes and E.Tassi, released under GPL version 2
or at your option any later version.

If --tptppath is given, instead of the problem file you can just give the 
problem name with the .p suffix (e.g. BOO001-1.p)

If --tptppath is not given, included files (i.e. axiom sets) are searched 
in the current directory only.

usage: matitaprover [options] problemfile";
  let hypotheses, goals = Tptp_cnf.parse ~tptppath:!tptppath !problem_file in
  let goal = match goals with [x] -> x | _ -> assert false in
  let _ = if !seconds > 0 then Unix.alarm !seconds else 0 in
  childs := 
    List.map 
      (fun f -> 
         let pid = Unix.fork () in 
         if pid = 0 then (exit (f ())) else pid)
    [ 
      (fun () -> worker `NRKBO ~useage:true ~printmsg:true goal hypotheses)
    ;
      (fun () -> worker `KBO ~useage:true ~printmsg:false goal hypotheses)
    ;
      (fun () -> worker `LPO ~useage:true ~printmsg:false goal hypotheses)
    ;
      (fun () -> worker `NRKBO ~useage:false ~printmsg:false goal hypotheses)
    ];
  let rec aux () =
    if List.length !childs = 0 then
      (fail_msg (); exit 1)
    else 
     match Unix.wait () with
     | p, (Unix.WEXITED 0 as s) -> 
         print_status p s;            
         killall !childs; exit 0;
     | p, s -> 
         print_status p s;            
         childs := List.filter ((<>)p) !childs; aux ()
  in
   aux ()
;;

main ()
