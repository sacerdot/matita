(* Copyright (C) 2004, HELM Team.
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
 * http://helm.cs.unibo.it/
 *)

(* $Id$ *)

open Printf

let nonvar uri = not (UriManager.uri_is_var uri)

module Constr = MetadataConstraints

exception Goal_is_not_an_equation

let debug = false
let debug_print s = if debug then prerr_endline (Lazy.force s)

let ( ** ) x y = int_of_float ((float_of_int x) ** (float_of_int y))

let signature_of_hypothesis context metasenv =
  let set, _ =
    List.fold_right
      (fun hyp (set,current_ctx) ->
        match hyp with
        | None -> set, hyp::current_ctx
        | Some (_, Cic.Decl t) -> 
            Constr.UriManagerSet.union set (Constr.constants_of t),
            hyp::current_ctx
        | Some (_, Cic.Def (t, _)) ->
            try 
              let ty,_ = 
                CicTypeChecker.type_of_aux' 
                  metasenv current_ctx t CicUniv.oblivion_ugraph 
              in
              let sort,_ = 
                CicTypeChecker.type_of_aux' 
                  metasenv current_ctx ty CicUniv.oblivion_ugraph 
              in
              let set = Constr.UriManagerSet.union set(Constr.constants_of ty)in
              match sort with
              | Cic.Sort Cic.Prop -> set, hyp::current_ctx
              | _ -> Constr.UriManagerSet.union set (Constr.constants_of t),
                     hyp::current_ctx
            with
            | CicTypeChecker.TypeCheckerFailure _ -> set, hyp::current_ctx)
      context (Constr.UriManagerSet.empty,[]) 
  in
  set
;;

let intersect uris siguris =
  let set1 = List.fold_right Constr.UriManagerSet.add uris Constr.UriManagerSet.empty in
  let set2 =
    List.fold_right Constr.UriManagerSet.add siguris Constr.UriManagerSet.empty
  in
  let inter = Constr.UriManagerSet.inter set1 set2 in
  List.filter (fun s -> Constr.UriManagerSet.mem s inter) uris

(* Profiling code
let at_most =
 let profiler = CicUtil.profile "at_most" in
 fun ~dbd ~where uri -> profiler.profile (Constr.at_most ~dbd ~where) uri

let sigmatch =
 let profiler = CicUtil.profile "sigmatch" in
 fun ~dbd ~facts ~where signature ->
  profiler.profile (MetadataConstraints.sigmatch ~dbd ~facts ~where) signature
*)
let at_most = Constr.at_most
let sigmatch = MetadataConstraints.sigmatch

let filter_uris_forward ~dbd (main, constants) uris =
  let main_uris =
    match main with
    | None -> []
    | Some (main, types) -> main :: types
  in
  let full_signature =
    List.fold_right Constr.UriManagerSet.add main_uris constants
  in
  List.filter (at_most ~dbd ~where:`Statement full_signature) uris

let filter_uris_backward ~dbd ~facts signature uris =
  let siguris =
    List.map snd 
      (sigmatch ~dbd ~facts ~where:`Statement signature)
  in
    intersect uris siguris 

let compare_goal_list proof goal1 goal2 =
  let _,metasenv, _subst, _,_, _ = proof in
  let (_, ey1, ty1) = CicUtil.lookup_meta goal1 metasenv in
  let (_, ey2, ty2) =  CicUtil.lookup_meta goal2 metasenv in
  let ty_sort1,_ = 
    CicTypeChecker.type_of_aux' metasenv ey1 ty1 CicUniv.oblivion_ugraph 
  in
  let ty_sort2,_ = 
    CicTypeChecker.type_of_aux' metasenv ey2 ty2 CicUniv.oblivion_ugraph 
  in
  let prop1 =
    let b,_ = 
      CicReduction.are_convertible 
	ey1 (Cic.Sort Cic.Prop) ty_sort1 CicUniv.oblivion_ugraph 
    in
      if b then 0
      else 1
  in
  let prop2 =
    let b,_ = 
      CicReduction.are_convertible 
	ey2 (Cic.Sort Cic.Prop) ty_sort2 CicUniv.oblivion_ugraph 
    in 
      if b then 0
      else 1
  in
  prop1 - prop2

(* experimental_hint is a version of hint for experimental 
    purposes. It uses auto_tac_verbose instead of auto tac.
    Auto_tac verbose also returns a substitution - for the moment 
    as a function from cic to cic, to be changed into an association
    list in the future -. This substitution is used to build a
    hash table of the inspected goals with their associated proofs.
    The cose is a cut and paste of the previous one: at the end 
    of the experimentation we shall make a choice. *)

let close_with_types s metasenv context =
  Constr.UriManagerSet.fold 
    (fun e bag -> 
      let t = CicUtil.term_of_uri e in
      let ty, _ = 
        CicTypeChecker.type_of_aux' metasenv context t CicUniv.oblivion_ugraph  
      in
      Constr.UriManagerSet.union bag (Constr.constants_of ty)) 
    s s

let close_with_constructors s metasenv context =
  Constr.UriManagerSet.fold 
    (fun e bag -> 
      let t = CicUtil.term_of_uri e in
      match t with
	  Cic.MutInd (uri,_,_)  
	| Cic.MutConstruct (uri,_,_,_) ->  
	    (match fst (CicEnvironment.get_obj CicUniv.oblivion_ugraph uri) with
		 Cic.InductiveDefinition(tl,_,_,_) ->
		   snd
		     (List.fold_left
			(fun (i,s) (_,_,_,cl) ->
			   let _,s =
			     List.fold_left 
			       (fun (j,s) _ -> 
				  let curi = UriManager.uri_of_uriref uri i (Some j) in
(*                                     prerr_endline ("adding " ^
 *                                     (UriManager.string_of_uri curi)); *)
				    j+1,Constr.UriManagerSet.add curi s) (1,s) cl in
			     (i+1,s)) (0,bag) tl)
	       | _ -> assert false)
	| _ -> bag)
    s s

(* Profiling code
let apply_tac_verbose =
 let profiler = CicUtil.profile "apply_tac_verbose" in
  fun ~term status -> profiler.profile (PrimitiveTactics.apply_tac_verbose ~term) status

let sigmatch =
 let profiler = CicUtil.profile "sigmatch" in
 fun ~dbd ~facts ?(where=`Conclusion) signature -> profiler.profile (Constr.sigmatch ~dbd ~facts ~where) signature

let cmatch' =
 let profiler = CicUtil.profile "cmatch'" in
 fun ~dbd ~facts signature -> profiler.profile (Constr.cmatch' ~dbd ~facts) signature
*)
let apply_tac_verbose = PrimitiveTactics.apply_tac_verbose
let cmatch' = Constr.cmatch'

(* used only by te old auto *)
let signature_of_goal ~(dbd:HSql.dbd) ((proof, goal) as _status) =
 let (_, metasenv, _subst, _, _, _) = proof in
 let (_, context, ty) = CicUtil.lookup_meta goal metasenv in
 let main, sig_constants = Constr.signature_of ty in
 let set = signature_of_hypothesis context metasenv in
 let set =
  match main with
     None -> set
   | Some (main,l) ->
      List.fold_right Constr.UriManagerSet.add (main::l) set in
 let set = Constr.UriManagerSet.union set sig_constants in
 let all_constants_closed = close_with_types set metasenv context in
 let uris =
  sigmatch ~dbd ~facts:false ~where:`Statement (None,all_constants_closed) in
 let uris = List.filter nonvar (List.map snd uris) in
 let uris = List.filter Hashtbl_equiv.not_a_duplicate uris in
  uris

let is_predicate u = 
    let ty, _ = 
      try CicTypeChecker.type_of_aux' [] []
        (CicUtil.term_of_uri u) CicUniv.oblivion_ugraph
      with CicTypeChecker.TypeCheckerFailure _ -> assert false
    in
    let rec check_last_pi = function
      | Cic.Prod (_,_,tgt) -> check_last_pi tgt
      | Cic.Sort Cic.Prop -> true
      | _ -> false
    in
    check_last_pi ty
;;

let only constants uri =
  prerr_endline (UriManager.string_of_uri uri);
  let t = CicUtil.term_of_uri uri in (* FIXME: write ty_of_term *)
  let ty,_ = CicTypeChecker.type_of_aux' [] [] t CicUniv.oblivion_ugraph in
  let consts = Constr.constants_of ty in
(*
  prerr_endline ("XXX " ^ UriManager.string_of_uri uri);
  Constr.UriManagerSet.iter (fun u -> prerr_endline (" - " ^
 UriManager.string_of_uri u)) consts;
  Constr.UriManagerSet.iter (fun u -> prerr_endline (" + " ^
  UriManager.string_of_uri u)) constants;*)
  Constr.UriManagerSet.subset consts constants 
;;

let rec types_of_equality = function
  | Cic.Appl [Cic.MutInd (uri, _, _); ty; _; _] 
    when (LibraryObjects.is_eq_URI uri) -> 
      let uri_set = Constr.constants_of ty in
      if Constr.UriManagerSet.equal uri_set Constr.UriManagerSet.empty then
	Constr.SetSet.empty
      else Constr.SetSet.singleton uri_set
  | Cic.Prod (_, s, t) -> 
      Constr.SetSet.union (types_of_equality s) (types_of_equality t)
  | _ -> Constr.SetSet.empty
;;

let types_for_equality metasenv goal =
  let (_, context, ty) = CicUtil.lookup_meta goal metasenv in
  let all = types_of_equality ty in
  let _, all = 
    List.fold_left
      (fun (i,acc) _ -> 	 
	 let ty, _ = 
           CicTypeChecker.type_of_aux' 
             metasenv context (Cic.Rel i) CicUniv.oblivion_ugraph in
	 let newty = types_of_equality ty in
	   (i+1,Constr.SetSet.union newty acc)) 
      (1,all) context
  in all
;;
	   
let signature_of metasenv goal = 
  let (_, context, ty) = CicUtil.lookup_meta goal metasenv in
  let ty_set = Constr.constants_of ty in
  let hyp_set = signature_of_hypothesis context metasenv in
  let set = Constr.UriManagerSet.union ty_set hyp_set in
    close_with_types
     (close_with_constructors (close_with_types set metasenv context)
	metasenv context)
    metasenv context


let universe_of_goal ~(dbd:HSql.dbd) apply_only metasenv goal =
  let (_, context, ty) = CicUtil.lookup_meta goal metasenv in
  let ty_set = Constr.constants_of ty in
  let hyp_set = signature_of_hypothesis context metasenv in
  let set = Constr.UriManagerSet.union ty_set hyp_set in
  let all_constants_closed = close_with_types set metasenv context in
  (* we split predicates from the rest *)
  let predicates, rest = 
    Constr.UriManagerSet.partition is_predicate all_constants_closed
  in
  let uris =
    Constr.UriManagerSet.fold
      (fun u acc -> 
         debug_print (lazy ("processing "^(UriManager.string_of_uri u)));
         let set_for_sigmatch = 
	   Constr.UriManagerSet.remove u all_constants_closed in
	 if LibraryObjects.is_eq_URI (UriManager.strip_xpointer u) then
	   (* equality has a special treatment *)
           (debug_print (lazy "special treatment");
	   let tfe =
	     Constr.SetSet.elements (types_for_equality metasenv goal) 
	   in
	     List.fold_left 
	       (fun acc l ->
		  let tyl = Constr.UriManagerSet.elements l in
                  debug_print (lazy ("tyl: "^(String.concat "\n" 
			(List.map UriManager.string_of_uri tyl))));
		  let set_for_sigmatch =
		    Constr.UriManagerSet.diff set_for_sigmatch l in
		  let uris =
		    sigmatch ~dbd ~facts:false ~where:`Statement 
		      (Some (u,tyl),set_for_sigmatch) in
		    acc @ uris) 
	       acc tfe)
	 else
           (debug_print (lazy "normal treatment");
           let uris =
             sigmatch ~dbd ~facts:false ~where:`Statement 
               (Some (u,[]),set_for_sigmatch)
           in
             acc @ uris))
      predicates []
  in
(*
  let uris =
    sigmatch ~dbd ~facts:false ~where:`Statement (None,all_constants_closed) 
  in
*)
  let uris = List.filter nonvar (List.map snd uris) in
  let uris = List.filter Hashtbl_equiv.not_a_duplicate uris in
  if apply_only then 
    List.filter (only all_constants_closed) uris 
  else uris
;;

let filter_out_predicate set ctx menv =
  Constr.UriManagerSet.filter (fun u -> not (is_predicate u)) set  
;;

let equations_for_goal ~(dbd:HSql.dbd) ?signature ((proof, goal) as _status) =
(*
  let to_string set =
    "{\n" ^
      (String.concat "\n"
         (Constr.UriManagerSet.fold
            (fun u l -> ("  "^UriManager.string_of_uri u)::l) set []))
    ^ "\n}"
  in
*)
 let (_, metasenv, _subst, _, _, _) = proof in
 let (_, context, ty) = CicUtil.lookup_meta goal metasenv in
 let main, sig_constants = 
   match signature with 
   | None -> Constr.signature_of ty 
   | Some s -> s
 in
(*  Printf.printf "\nsig_constants: %s\n\n" (to_string sig_constants); *)
(*  match main with *)
(*      None -> raise Goal_is_not_an_equation *)
(*    | Some (m,l) -> *)
 let l =
   let eq_URI =
    match LibraryObjects.eq_URI () with
       None -> None
     | Some s ->
        Some
         (UriManager.uri_of_string
          (UriManager.string_of_uri s ^ "#xpointer(1/1)"))
   in
   match eq_URI,main with
   | Some eq_URI, Some (m, l) when UriManager.eq m eq_URI -> m::l
   | _ -> []
 in
 (*Printf.printf "\nSome (m, l): %s, [%s]\n\n"
   (UriManager.string_of_uri (List.hd l))
   (String.concat "; " (List.map UriManager.string_of_uri (List.tl l)));
 *)
 (*        if m == UriManager.uri_of_string HelmLibraryObjects.Logic.eq_XURI then ( *)
 let set = signature_of_hypothesis context metasenv in
 (*          Printf.printf "\nsignature_of_hypothesis: %s\n\n" (to_string set); *)
 let set = Constr.UriManagerSet.union set sig_constants in
 let set = filter_out_predicate set context metasenv in
 let set = close_with_types set metasenv context in
 (*          Printf.printf "\ndopo close_with_types: %s\n\n" (to_string set); *)
 let set = close_with_constructors set metasenv context in
 (*          Printf.printf "\ndopo close_with_constructors: %s\n\n" (to_string set); *)
 let set_for_sigmatch = List.fold_right Constr.UriManagerSet.remove l set in
 let uris =
   sigmatch ~dbd ~facts:false ~where:`Statement (main,set_for_sigmatch) in
 let uris = List.filter nonvar (List.map snd uris) in
 let uris = List.filter Hashtbl_equiv.not_a_duplicate uris in
 let set = List.fold_right Constr.UriManagerSet.add l set in
 let uris = List.filter (only set) uris in
 uris
   (*        ) *)
   (*        else raise Goal_is_not_an_equation *)

let experimental_hint 
  ~(dbd:HSql.dbd) ?(facts=false) ?signature ((proof, goal) as status) =
  let (_, metasenv, _subst, _, _, _) = proof in
  let (_, context, ty) = CicUtil.lookup_meta goal metasenv in
  let (uris, (main, sig_constants)) =
    match signature with
    | Some signature -> 
	(sigmatch ~dbd ~facts signature, signature)
    | None -> 
	(cmatch' ~dbd ~facts ty, Constr.signature_of ty)
  in 
  let uris = List.filter nonvar (List.map snd uris) in
  let uris = List.filter Hashtbl_equiv.not_a_duplicate uris in
  let types_constants =
    match main with
    | None -> Constr.UriManagerSet.empty
    | Some (main, types) ->
        List.fold_right Constr.UriManagerSet.add (main :: types)
          Constr.UriManagerSet.empty
  in
  let all_constants =
    let hyp_and_sug =
      Constr.UriManagerSet.union
        (signature_of_hypothesis context metasenv) 
        sig_constants
    in
    let main = 
      match main with
      | None -> Constr.UriManagerSet.empty
      | Some (main,_) -> 
          let ty, _ = 
            CicTypeChecker.type_of_aux' 
              metasenv context (CicUtil.term_of_uri main)
              CicUniv.oblivion_ugraph
          in
          Constr.constants_of ty
    in
    Constr.UriManagerSet.union main hyp_and_sug
  in
(* Constr.UriManagerSet.iter debug_print hyp_constants; *)
  let all_constants_closed = close_with_types all_constants metasenv context in
  let other_constants = 
    Constr.UriManagerSet.diff all_constants_closed types_constants
  in
  debug_print (lazy "all_constants_closed");
  if debug then Constr.UriManagerSet.iter (fun s -> debug_print (lazy (UriManager.string_of_uri s))) all_constants_closed;
  debug_print (lazy "other_constants");
  if debug then Constr.UriManagerSet.iter (fun s -> debug_print (lazy (UriManager.string_of_uri s))) other_constants;
  let uris = 
    let pow = 2 ** (Constr.UriManagerSet.cardinal other_constants) in
    if ((List.length uris < pow) or (pow <= 0))
    then begin
      debug_print (lazy "MetadataQuery: large sig, falling back to old method");
      filter_uris_forward ~dbd (main, other_constants) uris
    end else
      filter_uris_backward ~dbd ~facts (main, other_constants) uris
  in 
  let rec aux = function
    | [] -> []
    | uri :: tl ->
        (let status' =
            try
              let (subst,(proof, goal_list)) =
                  (* debug_print (lazy ("STO APPLICANDO" ^ uri)); *)
                  apply_tac_verbose 
		    ~term:(CicUtil.term_of_uri uri)
                  status
              in
              let goal_list =
                List.stable_sort (compare_goal_list proof) goal_list
              in
              Some (uri, (subst,(proof, goal_list)))
            with ProofEngineTypes.Fail _ -> None
          in
          match status' with
          | None -> aux tl
          | Some status' -> status' :: aux tl)
  in
  List.stable_sort
    (fun (_,(_, (_, goals1))) (_,(_, (_, goals2))) ->
      Pervasives.compare (List.length goals1) (List.length goals2))
    (aux uris)

let new_experimental_hint 
  ~(dbd:HSql.dbd) ?(facts=false) ?signature ~universe
  ((proof, goal) as status)
=
  let (_, metasenv,  _subst, _, _, _) = proof in
  let (_, context, ty) = CicUtil.lookup_meta goal metasenv in
  let (uris, (main, sig_constants)) =
    match signature with
    | Some signature -> 
	(sigmatch ~dbd ~facts signature, signature)
    | None -> 
	(cmatch' ~dbd ~facts ty, Constr.signature_of ty) in 
  let universe =
   List.fold_left
    (fun res u -> Constr.UriManagerSet.add u res)
    Constr.UriManagerSet.empty universe in
  let uris =
   List.fold_left
    (fun res (_,u) -> Constr.UriManagerSet.add u res)
    Constr.UriManagerSet.empty uris in
  let uris = Constr.UriManagerSet.inter uris universe in
  let uris = Constr.UriManagerSet.elements uris in
  let rec aux = function
    | [] -> []
    | uri :: tl ->
        (let status' =
            try
              let (subst,(proof, goal_list)) =
                  (* debug_print (lazy ("STO APPLICANDO" ^ uri)); *)
                  apply_tac_verbose 
		    ~term:(CicUtil.term_of_uri uri)
                  status
              in
              let goal_list =
                List.stable_sort (compare_goal_list proof) goal_list
              in
              Some (uri, (subst,(proof, goal_list)))
            with ProofEngineTypes.Fail _ -> None
          in
          match status' with
          | None -> aux tl
          | Some status' -> status' :: aux tl)
  in
  List.stable_sort
    (fun (_,(_, (_, goals1))) (_,(_, (_, goals2))) ->
      Pervasives.compare (List.length goals1) (List.length goals2))
    (aux uris)

