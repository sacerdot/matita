(* Copyright (C) 2000, HELM Team.
 * 
 * This file is part of HELM, an Hypertextual, Electronic
 * Library of Mathematics, developed at the Computer Science
 * Department, University of Bologna, Italy.
 * 
 * HELM is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * HELM is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with HELM; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 * MA  02111-1307, USA.
 * 
 * For details, see the HELM World-Wide-Web page,
 * http://cs.unibo.it/helm/.
 *)

(*****************************************************************************)
(*                                                                           *)
(*                               PROJECT HELM                                *)
(*                                                                           *)
(*                      Enrico Tassi <tassi@cs.unibo.it>                     *)
(*                                 23/04/2004                                *)
(*                                                                           *)
(* This module implements the aciclic graph of universes.                    *)
(*                                                                           *)
(*****************************************************************************)

(* $Id$ *)

(*****************************************************************************)
(** open                                                                    **)
(*****************************************************************************)

open Printf

(*****************************************************************************)
(** Types and default values                                                **)
(*****************************************************************************)


type universe = int * UriManager.uri option 

let eq u1 u2 = 
  match u1,u2 with
  | (id1, Some uri1),(id2, Some uri2) -> 
      id1 = id2 && UriManager.eq uri1 uri2
  | (id1, None),(id2, None) -> id1 = id2
  | _ -> false
  
let compare (id1, uri1) (id2, uri2) = 
  let cmp = id1 - id2 in
  if cmp = 0 then
    match uri1,uri2 with
    | None, None -> 0 
    | Some _, None -> 1
    | None, Some _ -> ~-1
    | Some uri1, Some uri2 -> UriManager.compare uri1 uri2
  else
    cmp

module UniverseType = struct
  type t = universe
  let compare = compare
end
  
module SOF = Set.Make(UniverseType)
  
type entry = {
  eq_closure : SOF.t;
  ge_closure : SOF.t;
  gt_closure : SOF.t;
  in_gegt_of   : SOF.t;
  one_s_eq   : SOF.t;
  one_s_ge   : SOF.t;
  one_s_gt   : SOF.t;
}
    
module MAL = Map.Make(UniverseType)
  
type arc_type = GE | GT | EQ
    
type bag = entry MAL.t 
    
let empty_entry = {
  eq_closure=SOF.empty;
  ge_closure=SOF.empty;
  gt_closure=SOF.empty;
  in_gegt_of=SOF.empty;
  one_s_eq=SOF.empty;
  one_s_ge=SOF.empty;
  one_s_gt=SOF.empty;
}
let empty_bag = MAL.empty

let are_set_eq s1 s2 = 
  SOF.equal s1 s2

let are_entry_eq v1 v2 =
  (are_set_eq v1.gt_closure v2.gt_closure ) &&
  (are_set_eq v1.ge_closure v2.ge_closure ) &&
  (are_set_eq v1.eq_closure v2.eq_closure ) &&
  (*(are_set_eq v1.in_gegt_of v2.in_gegt_of ) &&*)
  (are_set_eq v1.one_s_ge v2.one_s_ge ) &&
  (are_set_eq v1.one_s_gt v2.one_s_gt ) &&
  (are_set_eq v1.one_s_eq v2.one_s_eq )

let are_ugraph_eq = MAL.equal are_entry_eq

(*****************************************************************************)
(** Pretty printings                                                        **)
(*****************************************************************************)

let string_of_universe (i,u) = 
  match u with
      Some u ->
        "(" ^ ((string_of_int i) ^ "," ^ (UriManager.string_of_uri u) ^ ")")
    | None -> "(" ^ (string_of_int i) ^ ",None)"

let string_of_universe_set l = 
  SOF.fold (fun x s -> s ^ (string_of_universe x) ^ " ") l ""

let string_of_node n =
  "{"^
  "eq_c: " ^ (string_of_universe_set n.eq_closure) ^ "; " ^ 
  "ge_c: " ^ (string_of_universe_set n.ge_closure) ^ "; " ^ 
  "gt_c: " ^ (string_of_universe_set n.gt_closure) ^ "; " ^ 
  "i_gegt: " ^ (string_of_universe_set n.in_gegt_of) ^ "}\n"

let string_of_arc (a,u,v) = 
  (string_of_universe u) ^ " " ^ a ^ " " ^ (string_of_universe v)
  
let string_of_mal m =
  let rc = ref "" in
  MAL.iter (fun k v ->  
    rc := !rc ^ sprintf "%s --> %s" (string_of_universe k) 
              (string_of_node v)) m;
  !rc

let string_of_bag b = 
  string_of_mal b

(*****************************************************************************)
(** Helpers                                                                 **)
(*****************************************************************************)

(* find the repr *)
let repr u m =
  try 
    MAL.find u m
  with
    Not_found -> empty_entry
    
(* FIXME: May be faster if we make it by hand *)
let merge_closures f nodes m =  
  SOF.fold (fun x i -> SOF.union (f (repr x m)) i ) nodes SOF.empty


(*****************************************************************************)
(** _fats implementation                                                    **)
(*****************************************************************************)

let rec closure_of_fast ru m =
  let eq_c = closure_eq_fast ru m in
  let ge_c = closure_ge_fast ru m in
  let gt_c = closure_gt_fast ru m in
    {
      eq_closure = eq_c;
      ge_closure = ge_c;
      gt_closure = gt_c;
      in_gegt_of = ru.in_gegt_of;
      one_s_eq = ru.one_s_eq;
      one_s_ge = ru.one_s_ge;
      one_s_gt = ru.one_s_gt
    }
      
and closure_eq_fast ru m = 
  let eq_c =
    let j = ru.one_s_eq in
    let _Uj = merge_closures (fun x -> x.eq_closure) j m in
    let one_step_eq = ru.one_s_eq in
      (SOF.union one_step_eq _Uj)
  in
    eq_c
      
and closure_ge_fast ru m =
  let ge_c = 
    let j = SOF.union ru.one_s_ge (SOF.union ru.one_s_gt ru.one_s_eq) in
    let _Uj = merge_closures (fun x -> x.ge_closure) j m in
    let _Ux = j in
      (SOF.union _Uj _Ux)
  in
    ge_c
      
and closure_gt_fast ru m =
  let gt_c =
    let j = ru.one_s_gt in
    let k = ru.one_s_ge in
    let l = ru.one_s_eq in
    let _Uj = merge_closures (fun x -> x.ge_closure) j m in
    let _Uk = merge_closures (fun x -> x.gt_closure) k m in
    let _Ul = merge_closures (fun x -> x.gt_closure) l m in
    let one_step_gt = ru.one_s_gt in
      (SOF.union (SOF.union (SOF.union _Ul one_step_gt) _Uk) _Uj)
  in
    gt_c
      
and print_rec_status u ru =
  print_endline ("Aggiusto " ^ (string_of_universe u) ^ 
                 "e ottengo questa chiusura\n " ^ (string_of_node ru))

and adjust_fast_aux adjusted u m =
  if SOF.mem u adjusted then m, adjusted else
  let adjusted = SOF.add u adjusted in
  let ru = repr u m in
  let gt_c = closure_gt_fast ru m in
  let ge_c = closure_ge_fast ru m in
  let eq_c = closure_eq_fast ru m in
  let changed_eq = not (are_set_eq eq_c ru.eq_closure) in
  let changed_gegt = 
    (not (are_set_eq gt_c ru.gt_closure)) || 
    (not (are_set_eq ge_c ru.ge_closure))
  in
    if ((not changed_gegt) &&  (not changed_eq)) then
      m, adjusted
    else
      begin
        let ru' = {
          eq_closure = eq_c;
          ge_closure = ge_c;
          gt_closure = gt_c;
          in_gegt_of = ru.in_gegt_of;
          one_s_eq = ru.one_s_eq;
          one_s_ge = ru.one_s_ge;
          one_s_gt = ru.one_s_gt}
        in
        let m = MAL.add u ru' m in
        let m, adjusted  =
          SOF.fold (fun x (m,adjusted) -> MAL.add x ru' m, SOF.add x adjusted) 
            (SOF.diff ru'.eq_closure adjusted) 
            (m,adjusted)
        in
        let m, adjusted  =
            SOF.fold (fun x (m,adjusted) -> adjust_fast_aux adjusted x m) 
              (SOF.diff ru'.in_gegt_of adjusted) 
              (m,adjusted)
        in
          m, adjusted 
      end

(*
and profiler_adj = HExtlib.profile "CicUniv.adjust_fast"
and adjust_fast x y = profiler_adj.HExtlib.profile (adjust_fast_aux x) y
*)
and adjust_fast x y = 
  fst(adjust_fast_aux SOF.empty x y)
        
and add_gt_arc_fast u v m =
  let ru = repr u m in
  if SOF.mem v ru.gt_closure then m else
  let ru' = {ru with one_s_gt = SOF.add v ru.one_s_gt} in
  let m' = MAL.add u ru' m in
  let rv = repr v m' in
  let rv' = {rv with in_gegt_of = SOF.add u rv.in_gegt_of} in
  let m'' = MAL.add v rv' m' in
    adjust_fast u m''
      
and add_ge_arc_fast u v m =
  let ru = repr u m in
  if SOF.mem v ru.ge_closure then m else
  let ru' = { ru with one_s_ge = SOF.add v ru.one_s_ge} in
  let m' = MAL.add u ru' m in
  let rv = repr v m' in
  let rv' = {rv with in_gegt_of = SOF.add u rv.in_gegt_of} in
  let m'' = MAL.add v rv' m' in
  adjust_fast u m''

and add_eq_arc_fast u v m =
  let ru = repr u m in
  if SOF.mem v ru.eq_closure then m else
  let rv = repr v m in 
  let ru' = {ru  with one_s_eq = SOF.add v ru.one_s_eq} in
  (*TESI: let ru' = {ru' with in_gegt_of = SOF.add v ru.in_gegt_of} in *)
  let m' = MAL.add u ru' m in
  let rv' = {rv  with one_s_eq = SOF.add u rv.one_s_eq} in
  (*TESI: let rv' = {rv' with in_gegt_of = SOF.add u rv.in_gegt_of} in *)
  let m'' = MAL.add v rv' m' in
    adjust_fast v (*(adjust_fast u*) m'' (* ) *)
;;



(*****************************************************************************)
(** Other real code                                                         **)
(*****************************************************************************)

exception UniverseInconsistency of string Lazy.t

let error arc node1 closure_type node2 closure =
  let s =
   lazy
    ("\n  ===== Universe Inconsistency detected =====\n\n" ^
     "   Unable to add\n" ^ 
     "\t" ^ (string_of_arc arc) ^ "\n" ^
     "   cause\n" ^ 
     "\t" ^ (string_of_universe node1) ^ "\n" ^
     "   is in the " ^ closure_type ^ " closure\n" ^
     "\t{" ^ (string_of_universe_set closure) ^ "}\n" ^ 
     "   of\n" ^ 
     "\t" ^ (string_of_universe node2) ^ "\n\n" ^
     "  ===== Universe Inconsistency detected =====\n") in
(*   prerr_endline (Lazy.force s); *)
  raise (UniverseInconsistency s)


let fill_empty_nodes_with_uri (g, already_contained,o) l uri =
  let fill_empty_universe u =
    match u with
        (i,None) -> (i,Some uri)
      | (i,Some _) as u -> u
  in
  let fill_empty_set s =
    SOF.fold (fun e s -> SOF.add (fill_empty_universe e) s) s SOF.empty 
  in
  let fill_empty_entry e = {
    eq_closure = (fill_empty_set e.eq_closure) ;
    ge_closure = (fill_empty_set e.ge_closure) ;
    gt_closure = (fill_empty_set e.gt_closure) ;
    in_gegt_of = (fill_empty_set e.in_gegt_of) ;
    one_s_eq = (fill_empty_set e.one_s_eq) ;
    one_s_ge = (fill_empty_set e.one_s_ge) ;
    one_s_gt = (fill_empty_set e.one_s_gt) ;
  } in  
  let m = g in
  let m' = MAL.fold (
    fun k v m -> 
      MAL.add (fill_empty_universe k) (fill_empty_entry v) m) m MAL.empty
  in
  let l' = List.map fill_empty_universe l in
    (m', already_contained,o),l'


(*****************************************************************************)
(** World interface                                                         **)
(*****************************************************************************)

type universe_graph = bag * UriManager.UriSet.t * bool
(* the graph , the cache of already merged ugraphs, oblivion? *)

let empty_ugraph = empty_bag, UriManager.UriSet.empty, false
let oblivion_ugraph = empty_bag, UriManager.UriSet.empty, true
(* FG: default choice for a ugraph ??? *)
let default_ugraph = oblivion_ugraph   

let current_index_anon = ref (-1)
let current_index_named = ref (-1)

let restart_numbering () = current_index_named := (-1) 

let fresh ?uri ?id () =
  let i =
    match uri,id with
    | None,None -> 
        current_index_anon := !current_index_anon + 1;
        !current_index_anon
    | None, Some _ -> assert false
    | Some _, None -> 
        current_index_named := !current_index_named + 1;
        !current_index_named
    | Some _, Some id -> id
  in
  (i,uri)

let name_universe u uri =
  match u with
  | (i, None) -> (i, Some uri)
  | u -> u
;;
  
let print_ugraph (g, _, o) = 
  if o then prerr_endline "oblivion universe" else
  prerr_endline (string_of_bag g)

let add_eq u v b =
  (* should we check to no add twice the same?? *)
  let m = b in
  let ru = repr u m in
  if SOF.mem v ru.gt_closure then
    error ("EQ",u,v) v "GT" u ru.gt_closure
  else
    begin
    let rv = repr v m in
    if SOF.mem u rv.gt_closure then
      error ("EQ",u,v) u "GT" v rv.gt_closure
    else
      add_eq_arc_fast u v b
    end

let add_ge u v b =
  (* should we check to no add twice the same?? *)
  let m = b in
  let rv = repr v m in
  if SOF.mem u rv.gt_closure then
    error ("GE",u,v) u "GT" v rv.gt_closure
  else
    add_ge_arc_fast u v b
  
let add_gt u v b =
  (* should we check to no add twice the same?? *)
  (* 
     FIXME : check the thesis... no need to check GT and EQ closure since the 
     GE is a superset of both 
  *)
  let m = b in
  let rv = repr v m in

  if u = v then
    error ("GT",u,v) u "==" v SOF.empty
  else
  
  (*if SOF.mem u rv.gt_closure then
    error ("GT",u,v) u "GT" v rv.gt_closure
  else
    begin*)
      if SOF.mem u rv.ge_closure then
        error ("GT",u,v) u "GE" v rv.ge_closure
      else
(*        begin
          if SOF.mem u rv.eq_closure then
            error ("GT",u,v) u "EQ" v rv.eq_closure
          else*)
            add_gt_arc_fast u v b
(*        end
    end*)

(*****************************************************************************)
(** START: Decomment this for performance comparisons                       **)
(*****************************************************************************)

let add_eq u v (b,already_contained,oblivion) =
        if oblivion then (b,already_contained,oblivion) else
  let rc = add_eq u v b in
    rc,already_contained,false

let add_ge u v (b,already_contained,oblivion) =
        if oblivion then (b,already_contained,oblivion) else
  let rc = add_ge u v b in
    rc,already_contained,false
    
let add_gt u v (b,already_contained,oblivion) =
        if oblivion then (b,already_contained,oblivion) else
  let rc = add_gt u v b in
    rc,already_contained,false
    
(* profiling code *) 
let profiler_eq = HExtlib.profile "CicUniv.add_eq"
let profiler_ge = HExtlib.profile "CicUniv.add_ge"
let profiler_gt = HExtlib.profile "CicUniv.add_gt"
let add_gt u v b = 
  profiler_gt.HExtlib.profile (fun _ -> add_gt u v b) ()
let add_ge u v b = 
  profiler_ge.HExtlib.profile (fun _ -> add_ge u v b) ()
let add_eq u v b = 
  profiler_eq.HExtlib.profile (fun _ -> add_eq u v b) ()


(* ugly *)
let rank = ref MAL.empty;;

let do_rank (b,_,_) =
   let keys = 
     MAL.fold 
       (fun k v acc -> 
          SOF.union acc (SOF.union (SOF.singleton k) 
            (SOF.union v.eq_closure (SOF.union v.gt_closure v.ge_closure))))
       b SOF.empty 
   in
   let keys = SOF.elements keys in
   let rec aux cache l =
      match l with
      | [] -> -1,cache
      | x::tl when List.mem_assoc x cache ->
          let height = List.assoc x cache in
          let rest, cache = aux cache tl in
          max rest height, cache
      | x::tl -> 
          let sons = SOF.elements (repr x b).gt_closure in
          let height,cache = aux cache sons in
          let height = height + 1 in
          let cache = (x,height) :: cache in
          let rest, cache = aux cache tl in
          max height rest, cache
   in
   let _, cache = aux [] keys in
   rank := List.fold_left (fun m (k,v) -> MAL.add k v m) MAL.empty cache;
   let res = ref [] in
   let resk = ref [] in
   MAL.iter 
     (fun k v -> 
       if not (List.mem v !res) then res := v::!res;
       resk := k :: !resk) !rank;
   !res, !resk
;;

let get_rank u = 
  try MAL.find u !rank 
  with Not_found -> 0 
  (* if the universe is not in the graph it means there are 
   * no contraints on it! thus it can be freely set to Type0 *)
;;

(*****************************************************************************)
(** END: Decomment this for performance comparisons                         **)
(*****************************************************************************)

(* TODO: uncomment l to gain a small speedup *)
let merge_ugraphs ~base_ugraph ~increment:(increment, uri_of_increment(*,l*)) =
  let merge_brutal (u,a,_) v = 
(*     prerr_endline ("merging graph: "^UriManager.string_of_uri
 *     uri_of_increment); *)
    let m1 = u in 
    let m2 = v in 
      MAL.fold (
        fun k v x -> 
          (SOF.fold (
             fun u x -> 
               let m = add_gt k u x in m) 
                (SOF.union v.one_s_gt v.gt_closure)
             (SOF.fold (
                fun u x -> 
                  let m = add_ge k u x in m) 
                    (SOF.union v.one_s_ge v.ge_closure)
                (SOF.fold (
                   fun u x ->
                     let m = add_eq k u x in m) 
                      (SOF.union v.one_s_eq v.eq_closure) x)))
          ) m1 m2 
  in
  let base, already_contained, oblivion = base_ugraph in
  let inc,_,oblivion2 = increment in
  if oblivion then
    base_ugraph      
  else if oblivion2 then
    increment
  else if MAL.is_empty base then
    increment
  else if 
    MAL.is_empty inc || 
    UriManager.UriSet.mem uri_of_increment already_contained 
  then
    base_ugraph
  else 
    (fun (x,_,_) -> x) (merge_brutal increment base_ugraph), 
(*
    List.fold_right UriManager.UriSet.add 
    (List.map (fun (_,x) -> HExtlib.unopt x) l)
*)
    (UriManager.UriSet.add uri_of_increment already_contained), false

(* profiling code; WARNING: the time spent during profiling can be
   greater than the profiled time 
let profiler_merge = HExtlib.profile "CicUniv.merge_ugraphs"
let merge_ugraphs ~base_ugraph ~increment =
  profiler_merge.HExtlib.profile 
  (fun _ -> merge_ugraphs ~base_ugraph ~increment) ()
*)

(*****************************************************************************)
(** Xml sesialization and parsing                                           **)
(*****************************************************************************)

let xml_of_universe name u = 
  match u with
  | (i,Some u) -> 
      Xml.xml_empty name [
        None,"id",(string_of_int i) ;
        None,"uri",(UriManager.string_of_uri u)]
  | (_,None) -> 
      raise (Failure "we can serialize only universes with uri")

let xml_of_set s =
  let l = 
    List.map (xml_of_universe "node") (SOF.elements s) 
  in
    List.fold_left (fun s x -> [< s ; x >] ) [<>] l
      
let xml_of_entry_content e =
  let stream_of_field f name =
    let eq_c = xml_of_set f in
    if eq_c != [<>] then
      Xml.xml_nempty name [] eq_c
    else
      [<>]
  in
  [<
    (stream_of_field e.eq_closure "eq_closure");
    (stream_of_field e.gt_closure "gt_closure");
    (stream_of_field e.ge_closure "ge_closure");
    (stream_of_field e.in_gegt_of "in_gegt_of");
    (stream_of_field e.one_s_eq "one_s_eq");
    (stream_of_field e.one_s_gt "one_s_gt");
    (stream_of_field e.one_s_ge "one_s_ge")
  >]

let xml_of_entry u e =
  let (i,u') = u in
  let u'' = 
    match u' with 
        Some x -> x 
      | None -> 
          raise (Failure "we can serialize only universes (entry) with uri")
  in
  let ent = Xml.xml_nempty "entry" [
    None,"id",(string_of_int i) ; 
    None,"uri",(UriManager.string_of_uri u'')] in
  let content = xml_of_entry_content e in
  ent content

let write_xml_of_ugraph filename (m,_,_) l =
    let tokens = 
      [< 
        Xml.xml_cdata "<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?>\n";
        Xml.xml_nempty "ugraph" [] 
          ([< (MAL.fold ( fun k v s -> [< s ; (xml_of_entry k v) >]) m [<>]) ; 
           (List.fold_left 
             (fun s u -> [< s ; xml_of_universe "owned_node" u >]) [<>] l) >])>]
    in
    Xml.pp ~gzip:true tokens (Some filename)

let univno = fst
let univuri = function 
  | _,None -> UriManager.uri_of_string "cic:/fake.con"
  | _,Some u -> u

 
let rec clean_ugraph m already_contained f =
  let m' = 
    MAL.fold (fun k v x -> if (f k) then MAL.add k v x else x ) m MAL.empty in
  let m'' =  MAL.fold (fun k v x -> 
    let v' = {
      eq_closure = SOF.filter f v.eq_closure;
      ge_closure = SOF.filter f v.ge_closure;
      gt_closure = SOF.filter f v.gt_closure;
      in_gegt_of = SOF.filter f v.in_gegt_of;
      one_s_eq = SOF.filter f v.one_s_eq;
      one_s_ge = SOF.filter f v.one_s_ge;
      one_s_gt = SOF.filter f v.one_s_gt
    } in 
    MAL.add k v' x ) m' MAL.empty in
  let e_l = 
    MAL.fold (fun k v l -> if v = empty_entry && not(f k) then
      begin
      SOF.add k l end else l) m'' SOF.empty
  in
    if not (SOF.is_empty e_l) then
      clean_ugraph 
        m'' already_contained (fun u -> (f u) && not (SOF.mem u e_l))
    else
      MAL.fold 
        (fun k v x -> if v <> empty_entry then MAL.add k v x else x) 
        m'' MAL.empty,
      already_contained

let clean_ugraph (m,a,o) l =
  assert(not o);
  let l = List.fold_right SOF.add l SOF.empty in
  let m, a = clean_ugraph m a (fun u -> SOF.mem u l) in
  m, a, o

let assigner_of = 
  function
    "ge_closure" -> (fun e u->{e with ge_closure=SOF.add u e.ge_closure})
  | "gt_closure" -> (fun e u->{e with gt_closure=SOF.add u e.gt_closure})
  | "eq_closure" -> (fun e u->{e with eq_closure=SOF.add u e.eq_closure})
  | "in_gegt_of"   -> (fun e u->{e with in_gegt_of  =SOF.add u e.in_gegt_of})
  | "one_s_ge"   -> (fun e u->{e with one_s_ge  =SOF.add u e.one_s_ge})
  | "one_s_gt"   -> (fun e u->{e with one_s_gt  =SOF.add u e.one_s_gt})
  | "one_s_eq"   -> (fun e u->{e with one_s_eq  =SOF.add u e.one_s_eq})
  | s -> raise (Failure ("unsupported tag " ^ s))
;;

let cb_factory m l = 
  let module XPP = XmlPushParser in
  let current_node = ref (0,None) in
  let current_entry = ref empty_entry in
  let current_assign = ref (assigner_of "in_gegt_of") in
  { XPP.default_callbacks with
    XPP.end_element = Some( fun name ->
      match name with
      | "entry" -> 
          m := MAL.add !current_node !current_entry !m;
          current_entry := empty_entry
      | _ -> ()
    );
    XPP.start_element = Some( fun name attlist ->
      match name with
      | "ugraph" -> ()
      | "entry" -> 
          let id = List.assoc "id" attlist in      
          let uri = List.assoc "uri" attlist in
          current_node := (int_of_string id,Some (UriManager.uri_of_string uri))
      | "node" -> 
          let id = int_of_string (List.assoc "id" attlist) in
          let uri = List.assoc "uri" attlist in        
            current_entry := !current_assign !current_entry 
              (id,Some (UriManager.uri_of_string uri))
      | "owned_node" -> 
          let id = int_of_string (List.assoc "id" attlist) in
          let uri = List.assoc "uri" attlist in        
          l := (id,Some (UriManager.uri_of_string uri)) :: !l
      | s -> current_assign := assigner_of s
    )
  }
;; 

let ugraph_and_univlist_of_xml filename =
  let module XPP = XmlPushParser in
  let result_map = ref MAL.empty in
  let result_list = ref [] in
  let cb = cb_factory result_map result_list in
  let xml_parser = XPP.create_parser cb in
  let xml_source = `Gzip_file filename in
  (try XPP.parse xml_parser xml_source
   with (XPP.Parse_error err) as exn -> raise exn);
  (!result_map,UriManager.UriSet.empty,false), !result_list


(*****************************************************************************)
(** the main, only for testing                                              **)
(*****************************************************************************)

(* 

type arc = Ge | Gt | Eq ;;

let randomize_actionlist n m =
  let ge_percent = 0.7 in
  let gt_percent = 0.15 in
  let random_step () =
    let node1 = Random.int m in
    let node2 = Random.int m in
    let op = 
      let r = Random.float 1.0 in
        if r < ge_percent then 
          Ge 
        else (if r < (ge_percent +. gt_percent) then 
          Gt 
        else 
          Eq) 
    in
      op,node1,node2      
  in
  let rec aux n =
    match n with 
        0 -> []
      | n -> (random_step ())::(aux (n-1))
  in
    aux n

let print_action_list l =
  let string_of_step (op,node1,node2) =
    (match op with
         Ge -> "Ge"
       | Gt -> "Gt"
       | Eq -> "Eq") ^ 
    "," ^ (string_of_int node1) ^ ","   ^ (string_of_int node2) 
  in
  let rec aux l =
    match l with 
        [] -> "]"
      | a::tl ->
          ";" ^ (string_of_step a) ^ (aux tl)
  in
  let body = aux l in
  let l_body = (String.length body) - 1 in
    prerr_endline ("[" ^ (String.sub body 1 l_body))
  
let debug = false
let d_print_endline = if debug then print_endline else ignore 
let d_print_ugraph = if debug then print_ugraph else ignore

let _ = 
  (if Array.length Sys.argv < 2 then
    prerr_endline ("Usage " ^ Sys.argv.(0) ^ " max_edges max_nodes"));
  Random.self_init ();
  let max_edges = int_of_string Sys.argv.(1) in
  let max_nodes = int_of_string Sys.argv.(2) in
  let action_listR = randomize_actionlist max_edges max_nodes in

  let action_list = [Ge,1,4;Ge,2,6;Ge,1,1;Eq,6,4;Gt,6,3] in
  let action_list = action_listR in
  
  print_action_list action_list;
  let prform_step ?(fast=false) (t,u,v) g =
    let f,str = 
      match t with
          Ge -> add_ge,">="
        | Gt -> add_gt,">"
        | Eq -> add_eq,"="
    in
      d_print_endline (
        "Aggiungo " ^ 
        (string_of_int u) ^
        " " ^ str ^ " " ^ 
        (string_of_int v));
      let g' = f ~fast (u,None) (v,None) g in
        (*print_ugraph g' ;*)
        g'
  in
  let fail = ref false in
  let time1 = Unix.gettimeofday () in
  let n_safe = ref 0 in
  let g_safe =  
    try 
      d_print_endline "SAFE";
      List.fold_left (
        fun g e -> 
          n_safe := !n_safe + 1;
          prform_step e g
      ) empty_ugraph action_list
    with
        UniverseInconsistency s -> fail:=true;empty_bag
  in
  let time2 = Unix.gettimeofday () in
  d_print_ugraph g_safe;
  let time3 = Unix.gettimeofday () in
  let n_test = ref 0 in
  let g_test = 
    try
      d_print_endline "FAST";
      List.fold_left (
        fun g e ->
          n_test := !n_test + 1;
          prform_step ~fast:true e g
      ) empty_ugraph action_list
    with
        UniverseInconsistency s -> empty_bag
  in
  let time4 = Unix.gettimeofday () in
  d_print_ugraph g_test;
    if are_ugraph_eq g_safe g_test && !n_test = !n_safe then
      begin
        let num_eq = 
          List.fold_left (
            fun s (e,_,_) -> 
              if e = Eq then s+1 else s 
          ) 0 action_list 
        in
        let num_gt = 
          List.fold_left (
            fun s (e,_,_) ->
              if e = Gt then s+1 else s
          ) 0 action_list
        in
        let num_ge = max_edges - num_gt - num_eq in
        let time_fast = (time4 -. time3) in
        let time_safe = (time2 -. time1) in
        let gap = ((time_safe -. time_fast) *. 100.0) /. time_safe in
        let fail = if !fail then 1 else 0 in
          print_endline 
            (sprintf 
               "OK %d safe %1.4f fast %1.4f %% %1.2f #eq %d #gt %d #ge %d %d" 
               fail time_safe time_fast gap num_eq num_gt num_ge !n_safe);
          exit 0
      end
    else
      begin
        print_endline "FAIL";
        print_ugraph g_safe;
        print_ugraph g_test;
        exit 1
      end
;;

 *)

let recons_univ u =
  match u with
  | i, None -> u
  | i, Some uri ->
      i, Some (UriManager.uri_of_string (UriManager.string_of_uri uri))

let recons_entry entry =
  let recons_set set =
    SOF.fold (fun univ set -> SOF.add (recons_univ univ) set) set SOF.empty
  in
  {
    eq_closure = recons_set entry.eq_closure;
    ge_closure = recons_set entry.ge_closure;
    gt_closure = recons_set entry.gt_closure;
    in_gegt_of = recons_set entry.in_gegt_of;
    one_s_eq = recons_set entry.one_s_eq;
    one_s_ge = recons_set entry.one_s_ge;
    one_s_gt = recons_set entry.one_s_gt;
  }

let recons_graph (graph,uriset,o) =
  MAL.fold
    (fun universe entry map ->
      MAL.add (recons_univ universe) (recons_entry entry) map)
    graph 
    MAL.empty,
  UriManager.UriSet.fold 
    (fun u acc -> 
      UriManager.UriSet.add 
        (UriManager.uri_of_string (UriManager.string_of_uri u)) acc) 
    uriset UriManager.UriSet.empty, o

let assert_univ u =
    match u with 
    | (_,None) ->
       raise (UniverseInconsistency (lazy "This universe graph has a hole"))
    | _ -> ()
    
let assert_univs_have_uri (graph,_,_) univlist =
  let assert_set s =
    SOF.iter (fun u -> assert_univ u) s
  in
  let assert_entry e =
    assert_set e.eq_closure;
    assert_set e.ge_closure;
    assert_set e.gt_closure;
    assert_set e.in_gegt_of;
    assert_set e.one_s_eq;
    assert_set e.one_s_ge;
    assert_set e.one_s_gt;
  in
  MAL.iter (fun k v -> assert_univ k; assert_entry v)graph;
  List.iter assert_univ univlist
  
let is_anon = function (_,None) -> true | _ -> false
  
(* EOF *)
