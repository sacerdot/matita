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

(* let _profiler = <:profiler<_profiler>>;; *)

(* $Id$ *)

open Utils;;
open Printf;;

let debug_print s = ();;(*prerr_endline (Lazy.force s);;*)

let check_disjoint_invariant subst metasenv msg =
  if (List.exists 
        (fun (i,_,_) -> (Subst.is_in_subst i subst)) metasenv)
  then 
    begin 
      prerr_endline ("not disjoint: " ^ msg);
      assert false
    end
;;

let rec check_irl start = function
  | [] -> true
  | None::tl -> check_irl (start+1) tl
  | (Some (Cic.Rel x))::tl ->
      if x = start then check_irl (start+1) tl else false
  | _ -> false
;;

let rec is_simple_term = function
  | Cic.Appl ((Cic.Meta _)::_) -> false
  | Cic.Appl l -> List.for_all is_simple_term l
  | Cic.Meta (i, l) -> let l = [] in check_irl 1 l
  | Cic.Rel _ -> true
  | Cic.Const _ -> true
  | Cic.MutInd (_, _, []) -> true
  | Cic.MutConstruct (_, _, _, []) -> true
  | _ -> false
;;

let locked menv i =
  List.exists (fun (j,_,_) -> i = j) menv
;;

let unification_simple locked_menv metasenv context t1 t2 ugraph =
  let module C = Cic in
  let module M = CicMetaSubst in
  let module U = CicUnification in
  let lookup = Subst.lookup_subst in
  let rec occurs_check subst what where =
    match where with
    | Cic.Meta(i,_) when i = what -> true
    | C.Appl l -> List.exists (occurs_check subst what) l
    | C.Meta _ ->
        let t = lookup where subst in
        if t <> where then occurs_check subst what t else false
    | _ -> false
  in
  let rec unif subst menv s t =
    let s = match s with C.Meta _ -> lookup s subst | _ -> s
    and t = match t with C.Meta _ -> lookup t subst | _ -> t
    
    in
    match s, t with
    | s, t when s = t -> subst, menv
    (* sometimes the same meta has different local contexts; this
       could create "cyclic" substitutions *)
    | C.Meta (i, _), C.Meta (j, _) when i=j ->  subst, menv
    | C.Meta (i, _), C.Meta (j, _) 
        when (locked locked_menv i) &&(locked locked_menv j) ->
        raise
          (U.UnificationFailure (lazy "Inference.unification.unif"))
    | C.Meta (i, _), C.Meta (j, _) when (locked locked_menv i) ->          
        unif subst menv t s
    | C.Meta (i, _), C.Meta (j, _) when (i > j) && not (locked locked_menv j) ->
        unif subst menv t s
    | C.Meta (i,_), t when occurs_check subst i t ->
        raise
          (U.UnificationFailure (lazy "Inference.unification.unif"))
    | C.Meta (i, l), t when (locked locked_menv i) -> 
        raise
          (U.UnificationFailure (lazy "Inference.unification.unif"))
    | C.Meta (i, l), t -> (
        try
          let _, _, ty = CicUtil.lookup_meta i menv in
          let subst = Subst.buildsubst i context t ty subst in
          subst, menv
        with CicUtil.Meta_not_found m ->
          let names = names_of_context context in
          (*debug_print
            (lazy*) prerr_endline 
               (Printf.sprintf "Meta_not_found %d!: %s %s\n%s\n\n%s" m
                  (CicPp.pp t1 names) (CicPp.pp t2 names)
                  (print_metasenv menv) (print_metasenv metasenv));
          assert false
      )
    | _, C.Meta _ -> unif subst menv t s
    | C.Appl (hds::_), C.Appl (hdt::_) when hds <> hdt ->
        raise (U.UnificationFailure (lazy "Inference.unification.unif"))
    | C.Appl (hds::tls), C.Appl (hdt::tlt) -> (
        try
          List.fold_left2
            (fun (subst', menv) s t -> unif subst' menv s t)
            (subst, menv) tls tlt
        with Invalid_argument _ ->
          raise (U.UnificationFailure (lazy "Inference.unification.unif"))
      )
    | _, _ ->
        raise (U.UnificationFailure (lazy "Inference.unification.unif"))
  in
  let subst, menv = unif Subst.empty_subst metasenv t1 t2 in
  let menv = Subst.filter subst menv in
  subst, menv, ugraph
;;

let profiler = HExtlib.profile "P/Inference.unif_simple[flatten]"
let profiler2 = HExtlib.profile "P/Inference.unif_simple[flatten_fast]"
let profiler3 = HExtlib.profile "P/Inference.unif_simple[resolve_meta]"
let profiler4 = HExtlib.profile "P/Inference.unif_simple[filter]"

let check_for_duplicates metas msg =
  let rec aux = function
    | [] -> true
    | (m,_,_)::tl -> 
	not (List.exists (fun (i, _, _) -> i = m) tl) && aux tl in
  let b = aux metas in
  if not b then  
    begin 
      prerr_endline ("DUPLICATI ---- " ^ msg);
      prerr_endline (CicMetaSubst.ppmetasenv [] metas);
      assert false
    end
  else b
;;

let check_metasenv msg menv =
  List.iter
    (fun (i,ctx,ty) -> 
       try ignore(CicTypeChecker.type_of_aux' menv ctx ty 
		  CicUniv.empty_ugraph)
       with 
	 | CicUtil.Meta_not_found _ -> 
	     prerr_endline (msg ^ CicMetaSubst.ppmetasenv [] menv);
	     assert false
	 | _ -> ()
    ) menv
;;

let unification_aux b metasenv1 metasenv2 context t1 t2 ugraph =
  let metasenv = metasenv1@metasenv2 in
  if Utils.debug_metas then
    begin
      ignore(check_for_duplicates metasenv "unification_aux");
      check_metasenv "unification_aux" metasenv;
    end;
  let subst, menv, ug =
    if not (is_simple_term t1) || not (is_simple_term t2) then (
      debug_print
        (lazy
           (Printf.sprintf "NOT SIMPLE TERMS: %s %s"
              (CicPp.ppterm t1) (CicPp.ppterm t2)));
      raise (CicUnification.UnificationFailure (lazy "Inference.unification.unif"))
    ) else
      if b then
        (* full unification *)
        unification_simple [] metasenv context t1 t2 ugraph
      else
        (* matching: metasenv1 is locked *)
        unification_simple metasenv1 metasenv context t1 t2 ugraph
  in
  if Utils.debug_res then
            ignore(check_disjoint_invariant subst menv "unif");
  (* let flatten subst = 
    List.map
      (fun (i, (context, term, ty)) ->
         let context = apply_subst_context subst context in
         let term = apply_subst subst term in
         let ty = apply_subst subst ty in  
           (i, (context, term, ty))) subst 
  in
  let flatten subst = profiler.HExtlib.profile flatten subst in
  let subst = flatten subst in *)
  if Utils.debug_metas then
    ignore(check_for_duplicates menv "unification_aux prima di apply_subst");
  let menv = Subst.apply_subst_metasenv subst menv in
  if Utils.debug_metas then
    (let _ = check_for_duplicates menv "unif_aux after" in
    check_metasenv "unification_aux after 1" menv);
  subst, menv, ug
;;

exception MatchingFailure;;

(** matching takes in input the _disjoint_ metasenv of t1 and  t2;
it perform unification in the union metasenv, then check that
the first metasenv has not changed *)
let matching metasenv1 metasenv2 context t1 t2 ugraph = 
  try 
    unification_aux false metasenv1 metasenv2 context t1 t2 ugraph
  with
    CicUnification.UnificationFailure _ -> 
      raise MatchingFailure
;;

let unification m1 m2 c t1 t2 ug = 
  let m1 =
    if (m1 = m2 && m1 <> []) then assert false
      (* (prerr_endline "eccoci 2"; []) *) else m1 in
  (*   
  prerr_endline (CicPp.ppterm t1);
  prerr_endline (CicPp.ppterm t2);
  prerr_endline "++++++++++"; *)
  try 
    unification_aux true m1 m2 c t1 t2 ug
  with exn -> 
    raise exn
;;

let get_stats () = "" (*<:show<Inference.>>*) ;;
