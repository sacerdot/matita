(* Copyright (C) 2005, HELM Team.
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

(* $Id$ *)

let time = false;;
let debug = false;;
let debug_metas = false;; 
let debug_res = false;;

let debug_print s = if debug then prerr_endline (Lazy.force s);;

let print_metasenv metasenv =
  String.concat "\n--------------------------\n"
    (List.map (fun (i, context, term) ->
                 (string_of_int i) ^ " [\n" ^ (CicPp.ppcontext context) ^
                   "\n] " ^  (CicPp.ppterm term))
       metasenv)
;;


let print_subst ?(prefix="\n") subst =
    String.concat prefix
     (List.map
       (fun (i, (c, t, ty)) ->
          Printf.sprintf "?%d -> %s : %s" i
            (CicPp.ppterm t) (CicPp.ppterm ty))
       subst)
;;  

type comparison = Lt | Le | Eq | Ge | Gt | Incomparable;;
    
let string_of_comparison = function
  | Lt -> "<"
  | Le -> "<="
  | Gt -> ">"
  | Ge -> ">="
  | Eq -> "="
  | Incomparable -> "I"

type environment = Cic.metasenv * Cic.context * CicUniv.universe_graph

module OrderedTerm =
struct
  type t = Cic.term
      
  let compare = Pervasives.compare
end

module TermSet = Set.Make(OrderedTerm);;
module TermMap = Map.Make(OrderedTerm);;

let symbols_of_term term =
  let module C = Cic in
  let rec aux map = function
    | C.Meta _ -> map
    | C.Appl l ->
        List.fold_left (fun res t -> (aux res t)) map l
    | t ->
        let map = 
          try
            let c = TermMap.find t map in
            TermMap.add t (c+1) map
          with Not_found ->
            TermMap.add t 1 map
        in
        map
  in
  aux TermMap.empty term
;;


let metas_of_term term =
  let module C = Cic in
  let rec aux = function
    | C.Meta _ as t -> TermSet.singleton t
    | C.Appl l ->
        List.fold_left (fun res t -> TermSet.union res (aux t)) TermSet.empty l
    | C.Lambda(n,s,t) ->
	TermSet.union (aux s) (aux t)
    | C.Prod(n,s,t) ->
	TermSet.union (aux s) (aux t)
    | C.LetIn(n,s,ty,t) ->
	TermSet.union (aux s) (TermSet.union (aux ty) (aux t))
    | t -> TermSet.empty (* TODO: maybe add other cases? *)
  in
  aux term
;;

let rec remove_local_context =
  function
    | Cic.Meta (i,_) -> Cic.Meta (i,[])
    | Cic.Appl l ->
       Cic.Appl(List.map remove_local_context l)
    | Cic.Prod (n,s,t) -> 
       Cic.Prod (n,remove_local_context s, remove_local_context t)
    | t -> t 


(************************* rpo ********************************)
let number = [
  UriManager.uri_of_string "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1)",3;
  UriManager.uri_of_string "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1/1)",6;
  UriManager.uri_of_string "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1/2)",9;
  HelmLibraryObjects.Peano.pred_URI, 12;
  HelmLibraryObjects.Peano.plus_URI, 15;
  HelmLibraryObjects.Peano.minus_URI, 18;
  HelmLibraryObjects.Peano.mult_URI, 21;
  UriManager.uri_of_string "cic:/matita/nat/nat/nat.ind#xpointer(1/1)",103;
  UriManager.uri_of_string "cic:/matita/nat/nat/nat.ind#xpointer(1/1/1)",106;
  UriManager.uri_of_string "cic:/matita/nat/nat/nat.ind#xpointer(1/1/2)",109;
  UriManager.uri_of_string "cic:/matita/nat/nat/pred.con",112;
  UriManager.uri_of_string "cic:/matita/nat/plus/plus.con",115;
  UriManager.uri_of_string "cic:/matita/nat/minus/minus.con",118;
  UriManager.uri_of_string "cic:/matita/nat/times/times.con",121;
  ]
;;

let atomic t =
  match t with
      Cic.Const _ 
    | Cic.MutInd _ 
    | Cic.MutConstruct _ 
    | Cic.Rel _ -> true
    | _ -> false

let sig_order_const t1 t2 =
  try
    let u1 = CicUtil.uri_of_term t1 in
    let u2 = CicUtil.uri_of_term t2 in  
    let n1 = List.assoc u1 number in
    let n2 = List.assoc u2 number in
    if n1 < n2 then Lt
    else if n1 > n2 then Gt
    else 
      begin
	prerr_endline ("t1 = "^(CicPp.ppterm t1));
	prerr_endline ("t2 = "^(CicPp.ppterm t2)); 
	assert false
      end
  with 
      Invalid_argument _ 
    | Not_found -> Incomparable

let sig_order t1 t2 =
  match t1, t2 with
      Cic.Rel n, Cic.Rel m when n < m -> Gt (* inverted order *)
    | Cic.Rel n, Cic.Rel m when n = m -> Incomparable
    | Cic.Rel n, Cic.Rel m when n > m -> Lt
    | Cic.Rel _, _ -> Gt
    | _, Cic.Rel _ -> Lt
    | _,_ -> sig_order_const t1 t2

let rec rpo_lt t1 t2 =
  let module C = Cic in 
  let first_trie =
    match t1,t2 with 
	C.Meta (_, _), C.Meta (_,_) -> false
      | C.Meta (_,_) , t2 -> TermSet.mem t1 (metas_of_term t2)
      | t1, C.Meta (_,_) -> false
      | C.Appl [h1;a1],C.Appl [h2;a2] when h1=h2 -> 
	  rpo_lt a1 a2
      | C.Appl (h1::arg1),C.Appl (h2::arg2) when h1=h2 ->
	  if lex_lt arg1 arg2 then
	    check_lt arg1 t2 
	  else false
      | C.Appl (h1::arg1),C.Appl (h2::arg2) -> 
	  (match sig_order h1 h2 with
	     | Lt -> check_lt arg1 t2
	     | _ -> false)
      | C.Appl (h1::arg1), t2 when atomic t2 ->
	  (match sig_order h1 t2 with
	     | Lt -> check_lt arg1 t2
	     | _ -> false)
      | t1 , C.Appl (h2::arg2) when atomic t1 ->
	  (match sig_order t1 h2 with
	     | Lt -> true
             | _ -> false )
      | C.Appl [] , _ -> assert false 
      | _ , C.Appl [] -> assert false
      | t1, t2 when (atomic t1 && atomic t2 && t1<>t2) ->
	  (match sig_order t1 t2 with
	     | Lt -> true
	     | _ -> false)
      | _,_ -> false
  in
  if first_trie then true else
  match t2 with
      C.Appl (_::args) ->
	List.exists (fun a -> t1 = a || rpo_lt t1 a) args
    | _ -> false
 
and lex_lt l1 l2 = 
  match l1,l2 with
      [],[] -> false
    | [],_ -> assert false
    | _, [] -> assert false
    | a1::l1, a2::l2 when a1 = a2 -> lex_lt l1 l2
    | a1::_, a2::_ -> rpo_lt a1 a2
 
and check_lt l t =
  List.fold_left 
    (fun b a -> b && (rpo_lt a t))
    true l
;;

let rpo t1 t2 =
  if rpo_lt t2 t1 then Gt
  else if rpo_lt t1 t2 then Lt
  else Incomparable


(*********************** fine rpo *****************************)

(* (weight of constants, [(meta, weight_of_meta)]) *)
type weight = int * (int * int) list;;

let string_of_weight (cw, mw) =
  let s =
    String.concat ", "
      (List.map (function (m, w) -> Printf.sprintf "(%d,%d)" m w) mw)
  in
  Printf.sprintf "[%d; %s]" cw s


let weight_of_term ?(consider_metas=true) ?(count_metas_occurrences=false) term =
  let module C = Cic in
  let vars_dict = Hashtbl.create 5 in
  let rec aux = function
    | C.Meta (metano, _) when consider_metas ->
        (try
           let oldw = Hashtbl.find vars_dict metano in
           Hashtbl.replace vars_dict metano (oldw+1)
         with Not_found ->
           Hashtbl.add vars_dict metano 1);
        if count_metas_occurrences then 1 else 0
    | C.Meta _ ->  (* "variables" are lighter than constants and functions...*)
        if count_metas_occurrences then 1 else 0         
    | C.Var (_, ens)
    | C.Const (_, ens)
    | C.MutInd (_, _, ens)
    | C.MutConstruct (_, _, _, ens) ->
        List.fold_left (fun w (u, t) -> (aux t) + w) 1 ens
         
    | C.Cast (t1, t2)
    | C.Lambda (_, t1, t2)
    | C.Prod (_, t1, t2)
    | C.LetIn (_, t1, _, t2) ->
        let w1 = aux t1 in
        let w2 = aux t2 in
        w1 + w2 + 1
          
    | C.Appl l -> List.fold_left (+) 0 (List.map aux l)
        
    | C.MutCase (_, _, outt, t, pl) ->
        let w1 = aux outt in
        let w2 = aux t in
        let w3 = List.fold_left (+) 0 (List.map aux pl) in
        w1 + w2 + w3 + 1
          
    | C.Fix (_, fl) ->
        List.fold_left (fun w (n, i, t1, t2) -> (aux t1) + (aux t2) + w) 1 fl
          
    | C.CoFix (_, fl) ->
        List.fold_left (fun w (n, t1, t2) -> (aux t1) + (aux t2) + w) 1 fl
          
    | _ -> 1
  in
  let w = aux term in
  let l =
    Hashtbl.fold (fun meta metaw resw -> (meta, metaw)::resw) vars_dict [] in
  let compare w1 w2 = 
    match w1, w2 with
    | (m1, _), (m2, _) -> m2 - m1 
  in 
  (w, List.sort compare l) (* from the biggest meta to the smallest (0) *)
;;


module OrderedInt = struct
  type t = int

  let compare = Pervasives.compare
end

module IntSet = Set.Make(OrderedInt)

let goal_symbols = ref TermSet.empty

let set_of_map m = 
  TermMap.fold (fun k _ s -> TermSet.add k s) m TermSet.empty
;;

let set_goal_symbols term = 
  let m = symbols_of_term term in
  goal_symbols := (set_of_map m)
;;

let symbols_of_eq (ty,left,right,_) = 
  let sty = set_of_map (symbols_of_term ty) in
  let sl = set_of_map (symbols_of_term left) in
  let sr = set_of_map (symbols_of_term right) in
  TermSet.union sty (TermSet.union sl sr)
;;

let distance sgoal seq =
  let s = TermSet.diff seq sgoal in
  TermSet.cardinal s
;;

let compute_equality_weight (ty,left,right,o) =
  let factor = 2 in
  match o with
    | Lt -> 
	let w, m = (weight_of_term 
	       ~consider_metas:true ~count_metas_occurrences:false right) in
	  w + (factor * (List.length m)) ;
    | Le -> assert false
    | Gt -> 
	let w, m = (weight_of_term 
	       ~consider_metas:true ~count_metas_occurrences:false left) in
	  w + (factor * (List.length m)) ;
  | Ge -> assert false
  | Eq 
  | Incomparable -> 
      let w1, m1 = (weight_of_term 
	       ~consider_metas:true ~count_metas_occurrences:false right) in
      let w2, m2 = (weight_of_term 
	       ~consider_metas:true ~count_metas_occurrences:false left) in
      w1 + w2 + (factor * (List.length m1)) + (factor * (List.length m2))
;;

let compute_equality_weight e =
  let w = compute_equality_weight e in
  let d = 0 in (* distance !goal_symbols (symbols_of_eq e) in *)
(*
  prerr_endline (Printf.sprintf "dist %s --- %s === %d" 
   (String.concat ", " (List.map (CicPp.ppterm) (TermSet.elements
     !goal_symbols)))
   (String.concat ", " (List.map (CicPp.ppterm) (TermSet.elements
     (symbols_of_eq e))))
   d
  );
*)
  w + d 
;;

(* old
let compute_equality_weight (ty,left,right,o) =
  let metasw = ref 0 in
  let weight_of t =
    let w, m = (weight_of_term 
		  ~consider_metas:true ~count_metas_occurrences:false t) in
    metasw := !metasw + (1 * (List.length m)) ;
    w
  in
  (* Warning: the following let cannot be expanded since it forces the
     right evaluation order!!!! *)
  let w = (weight_of ty) + (weight_of left) + (weight_of right) in 
  (* let w = weight_of (Cic.Appl [ty;left;right]) in *)
  w + !metasw
;;
*)

(* returns a "normalized" version of the polynomial weight wl (with type
 * weight list), i.e. a list sorted ascending by meta number,
 * from 0 to maxmeta. wl must be sorted descending by meta number. Example:
 * normalize_weight 5 (3, [(3, 2); (1, 1)]) ->
 *      (3, [(1, 1); (2, 0); (3, 2); (4, 0); (5, 0)]) *)
let normalize_weight maxmeta (cw, wl) =
  let rec aux = function
    | 0 -> []
    | m -> (m, 0)::(aux (m-1))
  in
  let tmpl = aux maxmeta in
  let wl =
    List.sort
      (fun (m, _) (n, _) -> Pervasives.compare m n)
      (List.fold_left
         (fun res (m, w) -> (m, w)::(List.remove_assoc m res)) tmpl wl)
  in
  (cw, wl)
;;


let normalize_weights (cw1, wl1) (cw2, wl2) =
  let rec aux wl1 wl2 =
    match wl1, wl2 with
    | [], [] -> [], []
    | (m, w)::tl1, (n, w')::tl2 when m = n ->
        let res1, res2 = aux tl1 tl2 in
        (m, w)::res1, (n, w')::res2
    | (m, w)::tl1, ((n, w')::_ as wl2) when m < n ->
        let res1, res2 = aux tl1 wl2 in
        (m, w)::res1, (m, 0)::res2
    | ((m, w)::_ as wl1), (n, w')::tl2 when m > n ->
        let res1, res2 = aux wl1 tl2 in
        (n, 0)::res1, (n, w')::res2
    | [], (n, w)::tl2 ->
        let res1, res2 = aux [] tl2 in
        (n, 0)::res1, (n, w)::res2
    | (m, w)::tl1, [] ->
        let res1, res2 = aux tl1 [] in
        (m, w)::res1, (m, 0)::res2
    | _, _ -> assert false
  in
  let cmp (m, _) (n, _) = compare m n in
  let wl1, wl2 = aux (List.sort cmp wl1) (List.sort cmp wl2) in
  (cw1, wl1), (cw2, wl2)
;;

        
let compare_weights ?(normalize=false)
    ((h1, w1) as weight1) ((h2, w2) as weight2)=
  let (h1, w1), (h2, w2) =
    if normalize then
      normalize_weights weight1 weight2
    else
      (h1, w1), (h2, w2)
  in
  let res, diffs =
    try
      List.fold_left2
        (fun ((lt, eq, gt), diffs) w1 w2 ->
           match w1, w2 with
           | (meta1, w1), (meta2, w2) when meta1 = meta2 ->
               let diffs = (w1 - w2) + diffs in 
               let r = compare w1 w2 in
               if r < 0 then (lt+1, eq, gt), diffs
               else if r = 0 then (lt, eq+1, gt), diffs
               else (lt, eq, gt+1), diffs
           | (meta1, w1), (meta2, w2) ->
               debug_print
                 (lazy
                    (Printf.sprintf "HMMM!!!! %s, %s\n"
                       (string_of_weight weight1) (string_of_weight weight2)));
               assert false)
        ((0, 0, 0), 0) w1 w2
    with Invalid_argument _ ->
      debug_print
        (lazy
           (Printf.sprintf "Invalid_argument: %s{%s}, %s{%s}, normalize = %s\n"
              (string_of_weight (h1, w1)) (string_of_weight weight1)
              (string_of_weight (h2, w2)) (string_of_weight weight2)
              (string_of_bool normalize)));
      assert false
  in
  let hdiff = h1 - h2 in 
  match res with
  | (0, _, 0) ->
      if hdiff < 0 then Lt
      else if hdiff > 0 then Gt
      else Eq (* Incomparable *)
  | (m, _, 0) ->
      if hdiff <= 0 then Lt
      else if (- diffs) >= hdiff then Le else Incomparable
  | (0, _, m) ->
      if hdiff >= 0 then Gt
      else if diffs >= (- hdiff) then Ge else Incomparable
  | (m, _, n) when m > 0 && n > 0 ->
      Incomparable
  | _ -> assert false 
;;


let rec aux_ordering ?(recursion=true) t1 t2 =
  let module C = Cic in
  let compare_uris u1 u2 =
    let res =
      compare (UriManager.string_of_uri u1) (UriManager.string_of_uri u2) in
    if res < 0 then Lt
    else if res = 0 then Eq
    else Gt
  in
  match t1, t2 with
  | C.Meta _, _
  | _, C.Meta _ -> Incomparable

  | t1, t2 when t1 = t2 -> Eq

  | C.Rel n, C.Rel m -> if n > m then Lt else Gt
  | C.Rel _, _ -> Lt
  | _, C.Rel _ -> Gt

  | C.Const (u1, _), C.Const (u2, _) -> compare_uris u1 u2
  | C.Const _, _ -> Lt
  | _, C.Const _ -> Gt

  | C.MutInd (u1, tno1, _), C.MutInd (u2, tno2, _) -> 
       let res =  compare_uris u1 u2 in
       if res <> Eq then res 
       else 
          let res = compare tno1 tno2 in
          if res = 0 then Eq else if res < 0 then Lt else Gt
  | C.MutInd _, _ -> Lt
  | _, C.MutInd _ -> Gt

  | C.MutConstruct (u1, tno1, cno1, _), C.MutConstruct (u2, tno2, cno2, _) ->
       let res =  compare_uris u1 u2 in
       if res <> Eq then res 
       else 
          let res = compare (tno1,cno1) (tno2,cno2) in
          if res = 0 then Eq else if res < 0 then Lt else Gt
  | C.MutConstruct _, _ -> Lt
  | _, C.MutConstruct _ -> Gt

  | C.Appl l1, C.Appl l2 when recursion ->
      let rec cmp t1 t2 =
        match t1, t2 with
        | [], [] -> Eq
        | _, [] -> Gt
        | [], _ -> Lt
        | hd1::tl1, hd2::tl2 ->
            let o = aux_ordering hd1 hd2 in
            if o = Eq then cmp tl1 tl2
            else o
      in
      cmp l1 l2
  | C.Appl (h1::t1), C.Appl (h2::t2) when not recursion ->
      aux_ordering h1 h2
        
  | t1, t2 ->
      debug_print
        (lazy
           (Printf.sprintf "These two terms are not comparable:\n%s\n%s\n\n"
              (CicPp.ppterm t1) (CicPp.ppterm t2)));
      Incomparable
;;


(* w1, w2 are the weights, they should already be normalized... *)
let nonrec_kbo_w (t1, w1) (t2, w2) =
  match compare_weights w1 w2 with
  | Le -> if aux_ordering t1 t2 = Lt then Lt else Incomparable
  | Ge -> if aux_ordering t1 t2 = Gt then Gt else Incomparable
  | Eq -> aux_ordering t1 t2
  | res -> res
;;

    
let nonrec_kbo t1 t2 =
  let w1 = weight_of_term t1 in
  let w2 = weight_of_term t2 in
  (*
  prerr_endline ("weight1 :"^(string_of_weight w1));
  prerr_endline ("weight2 :"^(string_of_weight w2)); 
  *)
  match compare_weights ~normalize:true w1 w2 with
  | Le -> if aux_ordering t1 t2 = Lt then Lt else Incomparable
  | Ge -> if aux_ordering t1 t2 = Gt then Gt else Incomparable
  | Eq -> aux_ordering t1 t2
  | res -> res
;;


let rec kbo t1 t2 =
  let aux = aux_ordering ~recursion:false in
  let w1 = weight_of_term t1
  and w2 = weight_of_term t2 in
  let rec cmp t1 t2 =
    match t1, t2 with
    | [], [] -> Eq
    | _, [] -> Gt
    | [], _ -> Lt
    | hd1::tl1, hd2::tl2 ->
        let o =
          kbo hd1 hd2
        in
        if o = Eq then cmp tl1 tl2
        else o
  in
  let comparison = compare_weights ~normalize:true w1 w2 in
  match comparison with
  | Le ->
      let r = aux t1 t2 in
      if r = Lt then Lt
      else if r = Eq then (
        match t1, t2 with
        | Cic.Appl (h1::tl1), Cic.Appl (h2::tl2) when h1 = h2 ->
            if cmp tl1 tl2 = Lt then Lt else Incomparable
        | _, _ ->  Incomparable
      ) else Incomparable
  | Ge ->
      let r = aux t1 t2 in
      if r = Gt then Gt
      else if r = Eq then (
        match t1, t2 with
        | Cic.Appl (h1::tl1), Cic.Appl (h2::tl2) when h1 = h2 ->
            if cmp tl1 tl2 = Gt then Gt else Incomparable
        | _, _ ->  Incomparable
      ) else Incomparable
  | Eq ->
      let r = aux t1 t2 in
      if r = Eq then (
        match t1, t2 with
        | Cic.Appl (h1::tl1), Cic.Appl (h2::tl2) when h1 = h2 ->
            cmp tl1 tl2
        | _, _ ->  Incomparable
      ) else r 
  | res -> res
;;
          
let rec ao t1 t2 =
  let get_hd t =
    match t with
	Cic.MutConstruct(uri,tyno,cno,_) -> Some(uri,tyno,cno)
      | Cic.Appl(Cic.MutConstruct(uri,tyno,cno,_)::_) -> 
	  Some(uri,tyno,cno)
      | _ -> None in
  let aux = aux_ordering ~recursion:false in
  let w1 = weight_of_term t1
  and w2 = weight_of_term t2 in
  let rec cmp t1 t2 =
    match t1, t2 with
    | [], [] -> Eq
    | _, [] -> Gt
    | [], _ -> Lt
    | hd1::tl1, hd2::tl2 ->
        let o =
          ao hd1 hd2
        in
        if o = Eq then cmp tl1 tl2
        else o
  in
  match get_hd t1, get_hd t2 with
      Some(_),None -> Lt
    | None,Some(_) -> Gt
    | _ ->
	let comparison = compare_weights ~normalize:true w1 w2 in
	  match comparison with
	    | Le ->
		let r = aux t1 t2 in
		  if r = Lt then Lt
		  else if r = Eq then (
		    match t1, t2 with
		      | Cic.Appl (h1::tl1), Cic.Appl (h2::tl2) when h1 = h2 ->
			  if cmp tl1 tl2 = Lt then Lt else Incomparable
		      | _, _ ->  Incomparable
		  ) else Incomparable
	    | Ge ->
		let r = aux t1 t2 in
		  if r = Gt then Gt
		  else if r = Eq then (
		    match t1, t2 with
		      | Cic.Appl (h1::tl1), Cic.Appl (h2::tl2) when h1 = h2 ->
			  if cmp tl1 tl2 = Gt then Gt else Incomparable
		      | _, _ ->  Incomparable
		  ) else Incomparable
	    | Eq ->
		let r = aux t1 t2 in
		  if r = Eq then (
		    match t1, t2 with
		      | Cic.Appl (h1::tl1), Cic.Appl (h2::tl2) when h1 = h2 ->
			  cmp tl1 tl2
		      | _, _ ->  Incomparable
		  ) else r 
	    | res -> res
;;

let names_of_context context = 
  List.map
    (function
       | None -> None
       | Some (n, e) -> Some n)
    context
;;


let rec lpo t1 t2 =
  let module C = Cic in
  match t1, t2 with
  | t1, t2 when t1 = t2 -> Eq
  | t1, (C.Meta _ as m) ->
      if TermSet.mem m (metas_of_term t1) then Gt else Incomparable
  | (C.Meta _ as m), t2 ->
      if TermSet.mem m (metas_of_term t2) then Lt else Incomparable
  | C.Appl (hd1::tl1), C.Appl (hd2::tl2) -> (
      let res =
        let f o r t =
          if r then true else
            match lpo t o with
            | Gt | Eq -> true
            | _ -> false
        in
        let res1 = List.fold_left (f t2) false tl1 in
        if res1 then Gt
        else let res2 = List.fold_left (f t1) false tl2 in
        if res2 then Lt
        else Incomparable
      in
      if res <> Incomparable then
        res
      else
        let f o r t =
          if not r then false else
            match lpo o t with
            | Gt -> true
            | _ -> false
        in
        match aux_ordering hd1 hd2 with
        | Gt ->
            let res = List.fold_left (f t1) false tl2 in
            if res then Gt
            else Incomparable
        | Lt ->
            let res = List.fold_left (f t2) false tl1 in
            if res then Lt
            else Incomparable
        | Eq -> (
            let lex_res =
              try
                List.fold_left2
                  (fun r t1 t2 -> if r <> Eq then r else lpo t1 t2)
                  Eq tl1 tl2
              with Invalid_argument _ ->
                Incomparable
            in
            match lex_res with
            | Gt ->
                if List.fold_left (f t1) false tl2 then Gt
                else Incomparable
            | Lt ->
                if List.fold_left (f t2) false tl1 then Lt
                else Incomparable
            | _ -> Incomparable
          )
        | _ -> Incomparable
    )
  | t1, t2 -> aux_ordering t1 t2
;;


(* settable by the user... *)
let compare_terms = ref nonrec_kbo;; 
(* let compare_terms = ref ao;; *)
(* let compare_terms = ref rpo;; *)

let guarded_simpl ?(debug=false) context t =
  if !compare_terms == nonrec_kbo then t
  else
    let t' = ProofEngineReduction.simpl context t in
    if t = t' then t else
      begin
	let simpl_order = !compare_terms t t' in
	 debug_print (lazy ("comparing "^(CicPp.ppterm t)^(CicPp.ppterm t')));
	if simpl_order = Gt then (if debug then prerr_endline "GT";t')
	else (if debug then prerr_endline "NO_GT";t)
      end
;;

type pos = Left | Right 

let string_of_pos = function
  | Left -> "Left"
  | Right -> "Right"
;;

let metas_of_term t = 
  List.map fst (CicUtil.metas_of_term t)
;;

