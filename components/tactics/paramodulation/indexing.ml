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

module Index = Equality_indexing.DT (* discrimination tree based indexing *)
(*
module Index = Equality_indexing.DT (* path tree based indexing *)
*)

let debug_print = Utils.debug_print;;

(* 
for debugging 
let check_equation env equation msg =
  let w, proof, (eq_ty, left, right, order), metas, args = equation in
  let metasenv, context, ugraph = env 
  let metasenv' = metasenv @ metas in
    try
      CicTypeChecker.type_of_aux' metasenv' context left ugraph;
      CicTypeChecker.type_of_aux' metasenv' context right ugraph;
      ()
    with 
        CicUtil.Meta_not_found _ as exn ->
          begin
            prerr_endline msg; 
            prerr_endline (CicPp.ppterm left);
            prerr_endline (CicPp.ppterm right);
            raise exn
          end 
*)

type retrieval_mode = Matching | Unification;;

let string_of_res ?env =
  function
      None -> "None"
    | Some (t, s, m, u, (p,e)) ->
        Printf.sprintf "Some: (%s, %s, %s)" 
          (Utils.string_of_pos p)
          (Equality.string_of_equality ?env e)
          (CicPp.ppterm t)
;;

let print_res ?env res = 
  prerr_endline 
    (String.concat "\n"
       (List.map (string_of_res ?env) res))
;;

let print_candidates ?env mode term res =
  let _ =
    match mode with
    | Matching ->
        prerr_endline ("| candidates Matching " ^ (CicPp.ppterm term))
    | Unification ->
        prerr_endline ("| candidates Unification " ^ (CicPp.ppterm term))
  in
  prerr_endline 
    (String.concat "\n"
       (List.map
          (fun (p, e) ->
             Printf.sprintf "| (%s, %s)" (Utils.string_of_pos p)
               (Equality.string_of_equality ?env e))
          res));
;;


let apply_subst = Subst.apply_subst

let index = Index.index
let remove_index = Index.remove_index
let in_index = Index.in_index
let empty = Index.empty 
let init_index = Index.init_index

let check_disjoint_invariant subst metasenv msg =
  if (List.exists 
        (fun (i,_,_) -> (Subst.is_in_subst i subst)) metasenv)
  then 
    begin 
      prerr_endline ("not disjoint: " ^ msg);
      assert false
    end
;;

let check_for_duplicates metas msg =
  let rec aux = function
    | [] -> true
    | (m,_,_)::tl -> not (List.exists (fun (i, _, _) -> i = m) tl) && aux tl in
  let b = aux metas in
    if not b then  
      begin 
      prerr_endline ("DUPLICATI " ^ msg);
      prerr_endline (CicMetaSubst.ppmetasenv [] metas);
      assert false
      end
    else ()
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

(* the metasenv returned by res must included in the original one,
due to matching. If it fails, it is probably because we are not 
demodulating with a unit equality *)

let not_unit_eq ctx eq =
  let (_,_,(ty,left,right,o),metas,_) = Equality.open_equality eq in
  let b = 
  List.exists 
    (fun (_,_,ty) ->
       try 
	 let s,_ = CicTypeChecker.type_of_aux' metas ctx ty CicUniv.oblivion_ugraph
	 in s = Cic.Sort(Cic.Prop)
       with _ -> 
	 prerr_endline ("ERROR typing " ^ CicPp.ppterm ty); assert false) metas
  in b
(*
if b then prerr_endline ("not a unit equality: " ^ Equality.string_of_equality eq); b *)
;;

let check_demod_res res metasenv msg =
  match res with
    | Some (_, _, menv, _, _) ->
	let b =
	  List.for_all
            (fun (i,_,_) -> 
	       (List.exists (fun (j,_,_) -> i=j) metasenv)) menv
	in
	  if (not b) then
	    begin
	      debug_print (lazy ("extended context " ^ msg));
	      debug_print (lazy (CicMetaSubst.ppmetasenv [] menv));
	    end;
	b
    | None -> false
;;

let check_res res msg =
  match res with
    | Some (t, subst, menv, ug, eq_found) ->
        let eqs = Equality.string_of_equality (snd eq_found) in
        check_metasenv msg menv;
        check_disjoint_invariant subst menv msg;
        check_for_duplicates menv (msg ^ "\nchecking " ^ eqs);
    | None -> ()
;;

let check_target bag context target msg =
  let w, proof, (eq_ty, left, right, order), metas,_ = 
    Equality.open_equality target in
  (* check that metas does not contains duplicates *)
  let eqs = Equality.string_of_equality target in
  let _ = check_for_duplicates metas (msg ^ "\nchecking " ^ eqs) in
  let actual = (Utils.metas_of_term left)@(Utils.metas_of_term right)
    @(Utils.metas_of_term eq_ty)@(Equality.metas_of_proof bag proof)  in
  let menv = List.filter (fun (i, _, _) -> List.mem i actual) metas in
  let _ = if menv <> metas then 
    begin 
      prerr_endline ("extra metas " ^ msg);
      prerr_endline (CicMetaSubst.ppmetasenv [] metas);
      prerr_endline "**********************";
      prerr_endline (CicMetaSubst.ppmetasenv [] menv);
      prerr_endline ("left: " ^ (CicPp.ppterm left));
      prerr_endline ("right: " ^ (CicPp.ppterm right)); 
      prerr_endline ("ty: " ^ (CicPp.ppterm eq_ty));
      assert false
    end
  else () in ()
(*
  try 
      ignore(CicTypeChecker.type_of_aux'
        metas context (Founif.build_proof_term proof) CicUniv.empty_ugraph)
  with e ->  
      prerr_endline msg;
      prerr_endline (Founif.string_of_proof proof);
      prerr_endline (CicPp.ppterm (Founif.build_proof_term proof));
      prerr_endline ("+++++++++++++left: " ^ (CicPp.ppterm left));
      prerr_endline ("+++++++++++++right: " ^ (CicPp.ppterm right)); 
      raise e 
*)


(* returns a list of all the equalities in the tree that are in relation
   "mode" with the given term, where mode can be either Matching or
   Unification.

   Format of the return value: list of tuples in the form:
   (position - Left or Right - of the term that matched the given one in this
     equality,
    equality found)
   
   Note that if equality is "left = right", if the ordering is left > right,
   the position will always be Left, and if the ordering is left < right,
   position will be Right.
*)

let get_candidates ?env mode tree term =
  let s = 
    match mode with
    | Matching -> 
        Index.retrieve_generalizations tree term
    | Unification -> 
        Index.retrieve_unifiables tree term
        
  in
  Index.PosEqSet.elements s
;;

(*
  finds the first equality in the index that matches "term", of type "termty"
  termty can be Implicit if it is not needed. The result (one of the sides of
  the equality, actually) should be not greater (wrt the term ordering) than
  term

  Format of the return value:

  (term to substitute, [Cic.Rel 1 properly lifted - see the various
                        build_newtarget functions inside the various
                        demodulation_* functions]
   substitution used for the matching,
   metasenv,
   ugraph, [substitution, metasenv and ugraph have the same meaning as those
   returned by CicUnification.fo_unif]
   (equality where the matching term was found, [i.e. the equality to use as
                                                rewrite rule]
    uri [either eq_ind_URI or eq_ind_r_URI, depending on the direction of
         the equality: this is used to build the proof term, again see one of
         the build_newtarget functions]
   ))
*)
let rec find_matches bag metasenv context ugraph lift_amount term termty =
  let module C = Cic in
  let module U = Utils in
  let module S = CicSubstitution in
  let module M = CicMetaSubst in
  let module HL = HelmLibraryObjects in
  let cmp = !Utils.compare_terms in
  let check = match termty with C.Implicit None -> false | _ -> true in
  function
    | [] -> None
    | candidate::tl ->
        let pos, equality = candidate in
        (* if not_unit_eq context equality then
	  begin
	    prerr_endline "not a unit";
	    prerr_endline (Equality.string_of_equality equality)
	  end; *)
        let (_, proof, (ty, left, right, o), metas,_) = 
          Equality.open_equality equality 
        in
        if Utils.debug_metas then 
          ignore(check_target bag context (snd candidate) "find_matches");
        if Utils.debug_res then 
          begin
            let c="eq = "^(Equality.string_of_equality (snd candidate)) ^ "\n"in
            let t="t = " ^ (CicPp.ppterm term) ^ "\n" in
            let m="metas = " ^ (CicMetaSubst.ppmetasenv [] metas) ^ "\n" in
            let ms="metasenv =" ^ (CicMetaSubst.ppmetasenv [] metasenv) ^ "\n" in
            let eq_uri = 
	      match LibraryObjects.eq_URI () with
		| Some (uri) -> uri
		| None -> raise (ProofEngineTypes.Fail (lazy "equality not declared")) in
            let p="proof = "^
              (CicPp.ppterm(Equality.build_proof_term bag eq_uri [] 0 proof))^"\n" 
            in

              check_for_duplicates metas "gia nella metas";
              check_for_duplicates metasenv "gia nel metasenv";
              check_for_duplicates (metasenv@metas) ("not disjoint"^c^t^m^ms^p)
          end;
        if check && not (fst (CicReduction.are_convertible
                                ~metasenv context termty ty ugraph)) then (
          find_matches bag metasenv context ugraph lift_amount term termty tl
        ) else
          let do_match c =
            let subst', metasenv', ugraph' =
              Founif.matching 
                metasenv metas context term (S.lift lift_amount c) ugraph
            in
            if Utils.debug_metas then
    	      check_metasenv "founif :" metasenv';
            Some (Cic.Rel(1+lift_amount),subst',metasenv',ugraph',candidate)
          in
          let c, other =
            if pos = Utils.Left then left, right
            else right, left
          in
          if o <> U.Incomparable then
            let res =
              try
                do_match c 
              with Founif.MatchingFailure ->
                find_matches bag metasenv context ugraph lift_amount term termty tl
            in
              if Utils.debug_res then ignore (check_res res "find1");
              res
          else
            let res =
              try do_match c 
              with Founif.MatchingFailure -> None
            in
	      if Utils.debug_res then ignore (check_res res "find2");
            match res with
            | Some (_, s, _, _, _) ->
                let c' = apply_subst s c in
                (* 
             let other' = U.guarded_simpl context (apply_subst s other) in *)
                let other' = apply_subst s other in
                let order = cmp c' other' in
                if order = U.Gt then
                  res
                else
                  find_matches bag
                    metasenv context ugraph lift_amount term termty tl
            | None ->
                find_matches bag metasenv context ugraph lift_amount term termty tl
;;

let find_matches metasenv context ugraph lift_amount term termty =
  find_matches metasenv context ugraph lift_amount term termty
;;

(*
  as above, but finds all the matching equalities, and the matching condition
  can be either Founif.matching or Inference.unification
*)
(* XXX termty unused *)
let rec find_all_matches ?(unif_fun=Founif.unification) ?(demod=false)
    metasenv context ugraph lift_amount term termty =
  let module C = Cic in
  let module U = Utils in
  let module S = CicSubstitution in
  let module M = CicMetaSubst in
  let module HL = HelmLibraryObjects in
  (* prerr_endline ("matching " ^  CicPp.ppterm term); *)
  let cmp x y = 
          let r = !Utils.compare_terms x y in
(*
          prerr_endline (
                  CicPp.ppterm x ^ "   " ^
                  Utils.string_of_comparison r ^ "   " ^ 
                       CicPp.ppterm y ); 
*)
          r
  in
  let check = match termty with C.Implicit None -> false | _ -> true in
  function
    | [] -> []
    | candidate::tl ->
        let pos, equality = candidate in 
        let (_,_,(ty,left,right,o),metas,_)= Equality.open_equality equality in
	if check && not (fst (CicReduction.are_convertible
                                ~metasenv context termty ty ugraph)) then (
          find_all_matches metasenv context ugraph lift_amount term termty tl
        ) else
        let do_match c =
          let subst', metasenv', ugraph' =
            unif_fun metasenv metas context term (S.lift lift_amount c) ugraph
          in
          (C.Rel (1+lift_amount),subst',metasenv',ugraph',candidate)
        in
        
        let c, other =
          if pos = Utils.Left then left, right
          else right, left
        in
        if o <> U.Incomparable then
          try
            let res = do_match c in
            res::(find_all_matches ~unif_fun metasenv context ugraph
                    lift_amount term termty tl)
          with
          | Founif.MatchingFailure
          | CicUnification.UnificationFailure _
          | CicUnification.Uncertain _ ->
              find_all_matches ~unif_fun metasenv context ugraph
                lift_amount term termty tl
        else
          try
            let res = do_match c in
            match res with
            | _, s, _, _, _ ->
                let c' = apply_subst s c
                and other' = apply_subst s other in
                let order = cmp c' other' in
                if (demod && order = U.Gt) ||
                   (not demod && (order <> U.Lt && order <> U.Le)) 
                then
                  res::(find_all_matches ~unif_fun metasenv context ugraph
                          lift_amount term termty tl)
                else
                  find_all_matches ~unif_fun metasenv context ugraph
                     lift_amount term termty tl
          with
          | Founif.MatchingFailure
          | CicUnification.UnificationFailure _
          | CicUnification.Uncertain _ ->
              find_all_matches ~unif_fun metasenv context ugraph
                lift_amount term termty tl
;;

let find_all_matches 
  ?unif_fun ?demod metasenv context ugraph lift_amount term termty l 
=
    find_all_matches 
      ?unif_fun ?demod metasenv context ugraph lift_amount term termty l 
  (*prerr_endline "CANDIDATES:";
  List.iter (fun (_,x)->prerr_endline (Founif.string_of_equality x)) l;
  prerr_endline ("MATCHING:" ^ CicPp.ppterm term ^ " are " ^ string_of_int
  (List.length rc));*)
;;
(*
  returns true if target is subsumed by some equality in table
*)
(*
let print_res l =
  prerr_endline (String.concat "\n" (List.map (fun (_, subst, menv, ug,
    ((pos,equation),_)) -> Equality.string_of_equality equation)l))
;;
*)

let subsumption_aux use_unification env table target = 
  let _, _, (ty, left, right, _), tmetas, _ = Equality.open_equality target in
  let _, context, ugraph = env in
  let metasenv = tmetas in
  let predicate, unif_fun = 
    if use_unification then
      Unification, Founif.unification
    else
      Matching, Founif.matching
  in
  let leftr =
    match left with
    | Cic.Meta _ when not use_unification -> []   
    | _ ->
        let leftc = get_candidates predicate table left in
        find_all_matches ~unif_fun
          metasenv context ugraph 0 left ty leftc
  in
  let rec ok what leftorright = function
    | [] -> None
    | (_, subst, menv, ug, (pos,equation))::tl ->
        let _, _, (_, l, r, o), m,_ = Equality.open_equality equation in
        try
          let other = if pos = Utils.Left then r else l in
          let what' = Subst.apply_subst subst what in
          let other' = Subst.apply_subst subst other in
          let subst', menv', ug' =
            unif_fun metasenv m context what' other' ugraph
          in
          (match Subst.merge_subst_if_possible subst subst' with
          | None -> ok what leftorright tl
          | Some s -> Some (s, equation, leftorright <> pos ))
        with 
        | Founif.MatchingFailure 
        | CicUnification.UnificationFailure _ -> ok what leftorright tl
  in
  match ok right Utils.Left leftr with
  | Some _ as res -> res
  | None -> 
      let rightr =
        match right with
          | Cic.Meta _ when not use_unification -> [] 
          | _ ->
              let rightc = get_candidates predicate table right in
                find_all_matches ~unif_fun
                  metasenv context ugraph 0 right ty rightc
      in
        ok left Utils.Right rightr 
;;

let subsumption x y z =
  subsumption_aux false x y z
;;

let unification x y z = 
  subsumption_aux true x y z
;;

(* the target must be disjoint from the equations in the table *)
let subsumption_aux_all use_unification env table target = 
  let _, _, (ty, left, right, _), tmetas, _ = Equality.open_equality target in
  let _, context, ugraph = env in
  let metasenv = tmetas in
  if Utils.debug_metas then
    check_for_duplicates metasenv "subsumption_aux_all";
  let predicate, unif_fun = 
    if use_unification then
      Unification, Founif.unification
    else
      Matching, Founif.matching
  in
  let leftr =
    match left with
    | Cic.Meta _ (*when not use_unification*) -> []   
    | _ ->
        let leftc = get_candidates predicate table left in
        find_all_matches ~unif_fun
          metasenv context ugraph 0 left ty leftc
  in
  let rightr =
        match right with
          | Cic.Meta _ (*when not use_unification*) -> [] 
          | _ ->
              let rightc = get_candidates predicate table right in
                find_all_matches ~unif_fun
                  metasenv context ugraph 0 right ty rightc
  in
  let rec ok_all what leftorright = function
    | [] -> []
    | (_, subst, menv, ug, (pos,equation))::tl ->
        let _, _, (_, l, r, o), m,_ = Equality.open_equality equation in
        try
          let other = if pos = Utils.Left then r else l in
          let what' = Subst.apply_subst subst what in
          let other' = Subst.apply_subst subst other in
          let subst', menv', ug' =
            unif_fun [] menv context what' other' ugraph
          in
          (match Subst.merge_subst_if_possible subst subst' with
          | None -> ok_all what leftorright tl
          | Some s -> 
	      (s, equation, leftorright <> pos )::(ok_all what leftorright tl))
        with 
        | Founif.MatchingFailure 
        | CicUnification.UnificationFailure _ -> (ok_all what leftorright tl)
  in
  (ok_all right Utils.Left leftr)@(ok_all left Utils.Right rightr )
;;

let subsumption_all x y z =
  subsumption_aux_all false x y z
;;

let unification_all x y z = 
  subsumption_aux_all true x y z
;;

let rec demodulation_aux bag ?from ?(typecheck=false) 
  metasenv context ugraph table lift_amount term =
  let module C = Cic in
  let module S = CicSubstitution in
  let module M = CicMetaSubst in
  let module HL = HelmLibraryObjects in
  if Utils.debug_metas then
    check_for_duplicates metasenv "in input a demodulation aux";
  let candidates = 
    get_candidates 
      ~env:(metasenv,context,ugraph) (* Unification *) Matching table term 
  in 
(*   let candidates = List.filter (fun _,x -> not (not_unit_eq context x)) candidates in *)
  let res =
    match term with
      | C.Meta _ -> None
      | term ->
	  let res = 
	    try
              let termty, ugraph =
		if typecheck then
		  CicTypeChecker.type_of_aux' metasenv context term ugraph
		else
		  C.Implicit None, ugraph
              in
		find_matches bag metasenv context ugraph 
		  lift_amount term termty candidates
            with _ ->  
	      prerr_endline "type checking error";
	      prerr_endline ("menv :\n" ^ CicMetaSubst.ppmetasenv [] metasenv);
	      prerr_endline ("term: " ^ (CicPp.ppterm term));
	      assert false;
              (* None *)
          in
	  let res = 
	    (if Utils.debug_res then
            ignore(check_res res "demod1");
	    if check_demod_res res metasenv "demod" then res else None) in
          if res <> None then
              res
            else
              match term with
                | C.Appl l ->
                    let res, ll = 
                      List.fold_left
                        (fun (res, tl) t ->
                           if res <> None then
                             (res, tl @ [S.lift 1 t])
                           else 
                             let r =
                               demodulation_aux bag ~from:"1" metasenv context ugraph table ~typecheck
                                 lift_amount t
                             in
                               match r with
                                 | None -> (None, tl @ [S.lift 1 t])
                                 | Some (rel, _, _, _, _) -> (r, tl @ [rel]))
                        (None, []) l
                    in (
                        match res with
                          | None -> None
                          | Some (_, subst, menv, ug, eq_found) ->
                              Some (C.Appl ll, subst, menv, ug, eq_found)
                      )
(*
                | C.Prod (nn, s, t) ->
                    let r1 =
                      demodulation_aux bag ~from:"2"
                        metasenv context ugraph table lift_amount s in (
                        match r1 with
                          | None ->
                              let r2 =
                                demodulation_aux bag metasenv
                                  ((Some (nn, C.Decl s))::context) ugraph
                                  table (lift_amount+1) t
                              in (
                                  match r2 with
                                    | None -> None
                                    | Some (t', subst, menv, ug, eq_found) ->
                                        Some (C.Prod (nn, (S.lift 1 s), t'),
                                              subst, menv, ug, eq_found)
                                )
                          | Some (s', subst, menv, ug, eq_found) ->
                              Some (C.Prod (nn, s', (S.lift 1 t)),
                                    subst, menv, ug, eq_found)
                      )
                | C.Lambda (nn, s, t) ->
                    prerr_endline "siam qui";
                    let r1 =
                      demodulation_aux bag
                        metasenv context ugraph table lift_amount s in (
                        match r1 with
                          | None ->
                              let r2 =
                                demodulation_aux bag metasenv
                                  ((Some (nn, C.Decl s))::context) ugraph
                                  table (lift_amount+1) t
                              in (
                                  match r2 with
                                    | None -> None
                                    | Some (t', subst, menv, ug, eq_found) ->
                                        Some (C.Lambda (nn, (S.lift 1 s), t'),
                                              subst, menv, ug, eq_found)
                                )
                          | Some (s', subst, menv, ug, eq_found) ->
                              Some (C.Lambda (nn, s', (S.lift 1 t)),
                                    subst, menv, ug, eq_found)
                      )
*)
                | t ->
                    None
  in
  if Utils.debug_res then ignore(check_res res "demod_aux output"); 
  res
;;

exception Foo

(** demodulation, when target is an equality *)
let rec demodulation_equality bag ?from eq_uri env table target =
  let module C = Cic in
  let module S = CicSubstitution in
  let module M = CicMetaSubst in
  let module HL = HelmLibraryObjects in
  let module U = Utils in
  let metasenv, context, ugraph = env in
  let w, proof, (eq_ty, left, right, order), metas, id = 
    Equality.open_equality target 
  in
  (* first, we simplify *)
(*   let right = U.guarded_simpl context right in *)
(*   let left = U.guarded_simpl context left in *)
(*   let order = !Utils.compare_terms left right in *)
(*   let stat = (eq_ty, left, right, order) in  *)
(*  let w = Utils.compute_equality_weight stat in*)
  (* let target = Equality.mk_equality (w, proof, stat, metas) in *)
  if Utils.debug_metas then 
    ignore(check_target bag context target "demod equalities input");
  let metasenv' = (* metasenv @ *) metas in
  
  let build_newtarget bag is_left (t, subst, menv, ug, eq_found) =
    
    if Utils.debug_metas then
      begin
        ignore(check_for_duplicates menv "input1");
        ignore(check_disjoint_invariant subst menv "input2");
        let substs = Subst.ppsubst subst in 
        ignore(check_target bag context (snd eq_found) ("input3" ^ substs))
      end;
    let pos, equality = eq_found in
    let (_, proof', 
        (ty, what, other, _), menv',id') = Equality.open_equality equality in
    (*
    let ty =
      try fst (CicTypeChecker.type_of_aux' menv' context what ugraph)
      with CicUtil.Meta_not_found _ -> ty 
    in *)
    let ty, eq_ty = apply_subst subst ty, apply_subst subst eq_ty in
    let what, other = if pos = Utils.Left then what, other else other, what in
    let newterm, newproof =
      let bo = 
        Utils.guarded_simpl context (apply_subst subst (S.subst other t)) in
(*      let name = C.Name ("x_Demod" ^ (string_of_int !demod_counter)) in*)
      let name = C.Name "x" in
      let bo' =
        let l, r = if is_left then t, S.lift 1 right else S.lift 1 left, t in
          C.Appl [C.MutInd (eq_uri, 0, []); S.lift 1 eq_ty; l; r]
      in
          (bo, (Equality.Step (subst,(Equality.Demodulation, id,(pos,id'),
          (Cic.Lambda (name, ty, bo'))))))
    in
    let newmenv = menv in
    let left, right = if is_left then newterm, right else left, newterm in
    let ordering = !Utils.compare_terms left right in
    let stat = (eq_ty, left, right, ordering) in
    let bag, res =
      let w = Utils.compute_equality_weight stat in
      Equality.mk_equality bag (w, newproof, stat,newmenv)
    in
    if Utils.debug_metas then 
      ignore(check_target bag context res "buildnew_target output");
    bag, res 
  in
  let res = 
    demodulation_aux bag ~from:"from3" metasenv' context ugraph table 0 left 
  in
  if Utils.debug_res then check_res res "demod result";
  let bag, newtarget = 
    match res with
    | Some t ->
        let bag, newtarget = build_newtarget bag true t in
          (* assert (not (Equality.meta_convertibility_eq target newtarget)); *)
          if (Equality.is_weak_identity newtarget) (* || *)
            (*Equality.meta_convertibility_eq target newtarget*) then
              bag, newtarget
          else 
            demodulation_equality bag ?from eq_uri env table newtarget
    | None ->
        let res = demodulation_aux bag metasenv' context ugraph table 0 right in
        if Utils.debug_res then check_res res "demod result 1"; 
          match res with
          | Some t ->
              let bag, newtarget = build_newtarget bag false t in
                if (Equality.is_weak_identity newtarget) ||
                  (Equality.meta_convertibility_eq target newtarget) then
                    bag, newtarget
                else
                   demodulation_equality bag ?from eq_uri env table newtarget
          | None ->
              bag, target
  in
  (* newmeta, newtarget *)
  bag, newtarget 
;;

(**
   Performs the beta expansion of the term "term" w.r.t. "table",
   i.e. returns the list of all the terms t s.t. "(t term) = t2", for some t2
   in table.
*)
let rec betaexpand_term 
  ?(subterms_only=false) metasenv context ugraph table lift_amount term 
=
  let module C = Cic in
  let module S = CicSubstitution in
  let module M = CicMetaSubst in
  let module HL = HelmLibraryObjects in
  
  let res, lifted_term = 
    match term with
    | C.Meta (i, l) ->
        let l = [] in
        let l', lifted_l =
          List.fold_right
            (fun arg (res, lifted_tl) ->
               match arg with
               | Some arg ->
                   let arg_res, lifted_arg =
                     betaexpand_term metasenv context ugraph table
                       lift_amount arg in
                   let l1 =
                     List.map
                       (fun (t, s, m, ug, eq_found) ->
                          (Some t)::lifted_tl, s, m, ug, eq_found)
                       arg_res
                   in
                   (l1 @
                      (List.map
                         (fun (l, s, m, ug, eq_found) ->
                            (Some lifted_arg)::l, s, m, ug, eq_found)
                         res),
                    (Some lifted_arg)::lifted_tl)
               | None ->
                   (List.map
                      (fun (r, s, m, ug, eq_found) ->
                         None::r, s, m, ug, eq_found) res,
                    None::lifted_tl)
            ) l ([], [])
        in
        let e =
          List.map
            (fun (l, s, m, ug, eq_found) ->
               (C.Meta (i, l), s, m, ug, eq_found)) l'
        in
        e, C.Meta (i, lifted_l)
          
    | C.Rel m ->
        [], if m <= lift_amount then C.Rel m else C.Rel (m+1)
          
    | C.Prod (nn, s, t) ->
        let l1, lifted_s =
          betaexpand_term metasenv context ugraph table lift_amount s in
        let l2, lifted_t =
          betaexpand_term metasenv ((Some (nn, C.Decl s))::context) ugraph
            table (lift_amount+1) t in
        let l1' =
          List.map
            (fun (t, s, m, ug, eq_found) ->
               C.Prod (nn, t, lifted_t), s, m, ug, eq_found) l1
        and l2' =
          List.map
            (fun (t, s, m, ug, eq_found) ->
               C.Prod (nn, lifted_s, t), s, m, ug, eq_found) l2 in
        l1' @ l2', C.Prod (nn, lifted_s, lifted_t)
          
    | C.Lambda (nn, s, t) ->
        let l1, lifted_s =
          betaexpand_term metasenv context ugraph table lift_amount s in
        let l2, lifted_t =
          betaexpand_term metasenv ((Some (nn, C.Decl s))::context) ugraph
            table (lift_amount+1) t in
        let l1' =
          List.map
            (fun (t, s, m, ug, eq_found) ->
               C.Lambda (nn, t, lifted_t), s, m, ug, eq_found) l1
        and l2' =
          List.map
            (fun (t, s, m, ug, eq_found) ->
               C.Lambda (nn, lifted_s, t), s, m, ug, eq_found) l2 in
        l1' @ l2', C.Lambda (nn, lifted_s, lifted_t)

    | C.Appl l ->
        let l', lifted_l =
          List.fold_left
            (fun (res, lifted_tl) arg ->
               let arg_res, lifted_arg =
                 betaexpand_term metasenv context ugraph table lift_amount arg
               in
               let l1 =
                 List.map
                   (fun (a, s, m, ug, eq_found) ->
                      a::lifted_tl, s, m, ug, eq_found)
                   arg_res
               in
               (l1 @
                  (List.map
                     (fun (r, s, m, ug, eq_found) ->
                        lifted_arg::r, s, m, ug, eq_found)
                     res),
                lifted_arg::lifted_tl)
            ) ([], []) (List.rev l)
        in
        (List.map
           (fun (l, s, m, ug, eq_found) -> (C.Appl l, s, m, ug, eq_found)) l',
         C.Appl lifted_l)

    | t -> [], (S.lift lift_amount t)
  in
  match term with
  | C.Meta (i, l) -> res, lifted_term
  | term ->
      let termty, ugraph =
       C.Implicit None, ugraph
(*          CicTypeChecker.type_of_aux' metasenv context term ugraph  *)
      in
      let candidates = get_candidates Unification table term in
      (* List.iter (fun (_,e) -> debug_print (lazy (Equality.string_of_equality e))) candidates; *)
      let r = 
        if subterms_only then 
          [] 
        else 
          find_all_matches
            metasenv context ugraph lift_amount term termty candidates
      in
      r @ res, lifted_term
;;

(**
   superposition_right
   returns a list of new clauses inferred with a right superposition step
   between the positive equation "target" and one in the "table" "newmeta" is
   the first free meta index, i.e. the first number above the highest meta
   index: its updated value is also returned
*)
let superposition_right bag
  ?(subterms_only=false) eq_uri (metasenv, context, ugraph) table target=
  let module C = Cic in
  let module S = CicSubstitution in
  let module M = CicMetaSubst in
  let module HL = HelmLibraryObjects in
  let module CR = CicReduction in
  let module U = Utils in 
  let w, eqproof, (eq_ty, left, right, ordering), newmetas,id = 
    Equality.open_equality target 
  in 
  if Utils.debug_metas then 
    ignore (check_target bag context target "superpositionright");
  let metasenv' = newmetas in
  let res1, res2 =
    match ordering with
    | U.Gt -> 
        fst (betaexpand_term ~subterms_only metasenv' context ugraph table 0 left), []
    | U.Lt -> 
        [], fst (betaexpand_term ~subterms_only metasenv' context ugraph table 0 right)
    | _ ->
        let res l r =
          List.filter
            (fun (_, subst, _, _, _) ->
               let subst = apply_subst subst in
               let o = !Utils.compare_terms (subst l) (subst r) in
               o <> U.Lt && o <> U.Le)
            (fst (betaexpand_term ~subterms_only metasenv' context ugraph table 0 l))
        in
        (res left right), (res right left)
  in
  let build_new bag ordering (bo, s, m, ug, eq_found) =
    if Utils.debug_metas then 
      ignore (check_target bag context (snd eq_found) "buildnew1" );
    
    let pos, equality =  eq_found in
    let (_, proof', (ty, what, other, _), menv',id') = 
      Equality.open_equality  equality in
    let what, other = if pos = Utils.Left then what, other else other, what in

    let ty, eq_ty = apply_subst s ty, apply_subst s eq_ty in
    let newgoal, newproof =
      (* qua *)
      let bo' =
        Utils.guarded_simpl context (apply_subst s (S.subst other bo)) 
      in
      let name = C.Name "x" in
      let bo'' =
        let l, r =
          if ordering = U.Gt then bo, S.lift 1 right else S.lift 1 left, bo in
        C.Appl [C.MutInd (eq_uri, 0, []); S.lift 1 eq_ty; l; r]
      in
      bo',
        Equality.Step 
          (s,(Equality.SuperpositionRight,
               id,(pos,id'),(Cic.Lambda(name,ty,bo''))))
    in
    let bag, newequality = 
      let left, right =
        if ordering = U.Gt then newgoal, apply_subst s right
        else apply_subst s left, newgoal in
      let neworder = !Utils.compare_terms left right in
      let newmenv = (* Founif.filter s *) m in
      let stat = (eq_ty, left, right, neworder) in
      let bag, eq' =
        let w = Utils.compute_equality_weight stat in
        Equality.mk_equality bag (w, newproof, stat, newmenv) in
      if Utils.debug_metas then 
        ignore (check_target bag context eq' "buildnew3");
      let bag, eq' = Equality.fix_metas bag eq' in
      if Utils.debug_metas then 
        ignore (check_target bag context eq' "buildnew4");
      bag, eq'
    in
    if Utils.debug_metas then 
      ignore(check_target bag context newequality "buildnew2"); 
    bag, newequality
  in
  let bag, new1 = 
    List.fold_right 
      (fun x (bag,acc) -> 
        let bag, e = build_new bag U.Gt x in
        bag, e::acc) res1 (bag,[]) 
  in
  let bag, new2 = 
    List.fold_right 
      (fun x (bag,acc) -> 
        let bag, e = build_new bag U.Lt x in
        bag, e::acc) res2 (bag,[]) 
  in
  let ok e = not (Equality.is_identity (metasenv', context, ugraph) e) in
  bag, List.filter ok (new1 @ new2)
;;

(** demodulation, when the target is a theorem *)
let rec demodulation_theorem bag env table theorem =
  let module C = Cic in
  let module S = CicSubstitution in
  let module M = CicMetaSubst in
  let module HL = HelmLibraryObjects in
  let eq_uri =
    match LibraryObjects.eq_URI() with
    | Some u -> u
    | None -> assert false in
  let metasenv, context, ugraph = env in
  let proof, theo, metas = theorem in
  let build_newtheorem (t, subst, menv, ug, eq_found) =
    let pos, equality = eq_found in
    let (_, proof', (ty, what, other, _), menv',id) = 
      Equality.open_equality equality in
    let peq = 
      match proof' with
      | Equality.Exact p -> p
      | _ -> assert false in
    let what, other = 
      if pos = Utils.Left then what, other else other, what in 
    let newtheo = apply_subst subst (S.subst other t) in
    let name = C.Name "x" in
    let body = apply_subst subst t in 
    let pred = C.Lambda(name,ty,body) in 
    let newproof =
      match pos with
        | Utils.Left ->
          Equality.mk_eq_ind eq_uri ty what pred proof other peq
        | Utils.Right ->
          Equality.mk_eq_ind eq_uri ty what pred proof other peq
    in
    newproof,newtheo
  in
  let res = demodulation_aux bag metas context ugraph table 0 theo in
  match res with
  | Some t ->
      let newproof, newtheo = build_newtheorem t in
      if Equality.meta_convertibility theo newtheo then
        newproof, newtheo
      else
        demodulation_theorem bag env table (newproof,newtheo,[])
  | None ->
      proof,theo
;;

(*****************************************************************************)
(**                         OPERATIONS ON GOALS                             **)
(**                                                                         **)
(**                DEMODULATION_GOAL & SUPERPOSITION_LEFT                   **)
(*****************************************************************************)

(* new: demodulation of non_equality terms *)
let build_newg bag context goal rule expansion =
  let goalproof,_,_ = goal in
  let (t,subst,menv,ug,eq_found) = expansion in
  let pos, equality = eq_found in
  let (_, proof', (ty, what, other, _), menv',id) = 
    Equality.open_equality equality in
  let what, other = if pos = Utils.Left then what, other else other, what in
  let newterm, newgoalproof =
    let bo = 
      Utils.guarded_simpl context 
        (apply_subst subst (CicSubstitution.subst other t)) 
    in
    let name = Cic.Name "x" in     
    let pred = apply_subst subst (Cic.Lambda (name,ty,t)) in 
    let newgoalproofstep = (rule,pos,id,subst,pred) in
    bo, (newgoalproofstep::goalproof)
  in
  let newmetasenv = (* Founif.filter subst *) menv in
  (newgoalproof, newmetasenv, newterm)
;;

let rec demod bag env table goal =
  let _,menv,t = goal in
  let _, context, ugraph = env in
  let res = demodulation_aux bag menv context ugraph table 0 t (~typecheck:false)in
  match res with
    | Some newt ->
	let newg = 
          build_newg bag context goal Equality.Demodulation newt 
        in
        let _,_,newt = newg in
        if Equality.meta_convertibility t newt then
          false, goal
        else
          true, snd (demod bag env table newg)
    | None -> 
	false, goal
;;

let open_goal g =
  match g with
  | (proof,menv,Cic.Appl[(Cic.MutInd(uri,0,_)) as eq;ty;l;r]) -> 
      (* assert (LibraryObjects.is_eq_URI uri); *)
      proof,menv,eq,ty,l,r
  | _ -> assert false

let ty_of_goal (_,_,ty) = ty ;;

(* checks if two goals are metaconvertible *)
let goal_metaconvertibility_eq g1 g2 = 
  Equality.meta_convertibility (ty_of_goal g1) (ty_of_goal g2)
;;

(* when the betaexpand_term function is called on the left/right side of the
 * goal, the predicate has to be fixed
 * C[x] ---> (eq ty unchanged C[x])
 * [posu] is the side of the [unchanged] term in the original goal
 *)

let fix_expansion goal posu (t, subst, menv, ug, eq_f) = 
  let _,_,eq,ty,l,r = open_goal goal in
  let unchanged = if posu = Utils.Left then l else r in
  let unchanged = CicSubstitution.lift 1 unchanged in
  let ty = CicSubstitution.lift 1 ty in
  let pred = 
    match posu with
    | Utils.Left -> Cic.Appl [eq;ty;unchanged;t]
    | Utils.Right -> Cic.Appl [eq;ty;t;unchanged]
  in
  (pred, subst, menv, ug, eq_f)
;;

(* ginve the old [goal], the side that has not changed [posu] and the 
 * expansion builds a new goal *)
let build_newgoal bag context goal posu rule expansion =
  let goalproof,_,_,_,_,_ = open_goal goal in
  let (t,subst,menv,ug,eq_found) = fix_expansion goal posu expansion in
  let pos, equality = eq_found in
  let (_, proof', (ty, what, other, _), menv',id) = 
    Equality.open_equality equality in
  let what, other = if pos = Utils.Left then what, other else other, what in
  let newterm, newgoalproof =
    let bo = 
      Utils.guarded_simpl context 
        (apply_subst subst (CicSubstitution.subst other t)) 
    in
    let name = Cic.Name "x" in 
    let pred = apply_subst subst (Cic.Lambda (name,ty,t)) in 
    let newgoalproofstep = (rule,pos,id,subst,pred) in
    bo, (newgoalproofstep::goalproof)
  in
  let newmetasenv = (* Founif.filter subst *) menv in
  (newgoalproof, newmetasenv, newterm)
;;

(**
   superposition_left 
   returns a list of new clauses inferred with a left superposition step
   the negative equation "target" and one of the positive equations in "table"
*)
let superposition_left bag (metasenv, context, ugraph) table goal = 
  let names = Utils.names_of_context context in
  let proof,menv,eq,ty,l,r = open_goal goal in
  let c = !Utils.compare_terms l r in
  let newgoals = 
    if c = Utils.Incomparable then
      begin
      let expansionsl, _ = betaexpand_term menv context ugraph table 0 l in
      let expansionsr, _ = betaexpand_term menv context ugraph table 0 r in
      (* prerr_endline "incomparable"; 
      prerr_endline (string_of_int (List.length expansionsl));
      prerr_endline (string_of_int (List.length expansionsr));
      *)
      List.map (build_newgoal bag context goal Utils.Right Equality.SuperpositionLeft) expansionsl
      @
      List.map (build_newgoal bag context goal Utils.Left Equality.SuperpositionLeft) expansionsr
      end
    else
        match c with 
        | Utils.Gt -> 
            let big,small,possmall = l,r,Utils.Right in
            let expansions, _ = betaexpand_term menv context ugraph table 0 big in
            List.map 
              (build_newgoal bag context goal possmall Equality.SuperpositionLeft) 
              expansions
        | Utils.Lt -> (* prerr_endline "LT"; *) 
            let big,small,possmall = r,l,Utils.Left in
            let expansions, _ = betaexpand_term menv context ugraph table 0 big in
            List.map 
              (build_newgoal bag context goal possmall Equality.SuperpositionLeft) 
              expansions
        | Utils.Eq -> []
        | _ ->
            prerr_endline 
              ("NOT GT, LT NOR EQ : "^CicPp.pp l names^" - "^CicPp.pp r names);
            assert false
  in
  (* rinfresco le meta *)
  List.fold_right
    (fun g (b,acc) -> 
       let b,g = Equality.fix_metas_goal b g in 
       b,g::acc) 
    newgoals (bag,[])
;;

(** demodulation, when the target is a goal *)
let rec demodulation_goal bag env table goal =
  let goalproof,menv,_,_,left,right = open_goal goal in
  let _, context, ugraph = env in
(*  let term = Utils.guarded_simpl (~debug:true) context term in*)
  let do_right () = 
      let resright = demodulation_aux bag menv context ugraph table 0 right in
      match resright with
      | Some t ->
          let newg = 
            build_newgoal bag context goal Utils.Left Equality.Demodulation t 
          in
          if goal_metaconvertibility_eq goal newg then
            false, goal
          else
            true, snd (demodulation_goal bag env table newg)
      | None -> false, goal
  in
  let resleft = demodulation_aux bag menv context ugraph table 0 left in
  match resleft with
  | Some t ->
      let newg = build_newgoal bag context goal Utils.Right Equality.Demodulation t in
      if goal_metaconvertibility_eq goal newg then
        do_right ()
      else
        true, snd (demodulation_goal bag env table newg)
  | None -> do_right ()
;;

(* returns all the 1 step demodulations *)
module C = Cic;; 
module S = CicSubstitution;;

let rec demodulation_all_aux 
  metasenv context ugraph table lift_amount term 
=
  let candidates = 
    get_candidates ~env:(metasenv,context,ugraph) Matching table term 
  in
  match term with
  | C.Meta _ -> []
  | _ ->
      let termty, ugraph = C.Implicit None, ugraph in
      let res =
        find_all_matches 
          ~unif_fun:Founif.matching ~demod:true
            metasenv context ugraph lift_amount term termty candidates
      in
      match term with
      | C.Appl l ->
         let res, _, _, _ = 
           List.fold_left
            (fun (res,b,l,r) t ->
               if not b then res,b,l,r
               else
                 let demods_for_t = 
                   demodulation_all_aux 
                     metasenv context ugraph table lift_amount t
                 in
                 let b = demods_for_t = [] in
                 res @  
                   List.map 
                    (fun (rel, s, m, ug, c) -> 
                      (Cic.Appl (l@[rel]@List.tl r), s, m, ug, c))
                   demods_for_t, b, l@[List.hd r], List.tl r)
            (res, true, [], List.map (S.lift 1) l) l
         in
         res
      | t -> res
;;

let demod_all steps bag env table goal =
  let _, context, ugraph = env in
  let is_visited l (_,_,t) = 
    List.exists (fun (_,_,s) -> Equality.meta_convertibility s t) l 
  in
  let rec aux steps visited nf bag = function
    | _ when steps = 0 -> visited, bag, nf
    | [] -> visited, bag, nf
    | goal :: rest when is_visited visited goal-> aux steps visited nf bag rest
    | goal :: rest ->
        let visited = goal :: visited in
        let _,menv,t = goal in
        let res = demodulation_all_aux menv context ugraph table 0 t in
        let steps = if res = [] then steps-1 else steps in
        let new_goals = 
          List.map (build_newg bag context goal Equality.Demodulation) res 
        in
        let nf = if new_goals = [] then goal :: nf else nf in
        aux steps visited nf bag (new_goals @ rest)
  in
  aux steps [] [] bag [goal] 
;;

let combine_demodulation_proofs bag env goal (pl,ml,l) (pr,mr,r) =
  let proof,m,eq,ty,left,right = open_goal goal in
  let pl = 
    List.map 
      (fun (rule,pos,id,subst,pred) -> 
        let pred = 
          match pred with
          | Cic.Lambda (name,src,tgt) ->
              Cic.Lambda (name,src, 
                Cic.Appl[eq;ty;tgt;CicSubstitution.lift 1 right])
          | _ -> assert false                 
        in
        rule,pos,id,subst,pred)
      pl
  in
  let pr = 
    List.map 
      (fun (rule,pos,id,subst,pred) -> 
        let pred = 
          match pred with
          | Cic.Lambda (name,src,tgt) ->
              Cic.Lambda (name,src, 
                Cic.Appl[eq;ty;CicSubstitution.lift 1 l;tgt])
          | _ -> assert false                 
        in
        rule,pos,id,subst,pred)
      pr
  in
  (pr@pl@proof, m, Cic.Appl [eq;ty;l;r])
;;

let demodulation_all_goal bag env table goal maxnf =
  let proof,menv,eq,ty,left,right = open_goal goal in
  let v1, bag, l_demod = demod_all maxnf bag env table ([],menv,left) in
  let v2, bag, r_demod = demod_all maxnf bag env table ([],menv,right) in
  let l_demod = if l_demod = [] then [ [], menv, left ] else l_demod in
  let r_demod = if r_demod = [] then [ [], menv, right ] else r_demod in
  List.fold_left
    (fun acc (_,_,l as ld) -> 
       List.fold_left 
           (fun acc (_,_,r as rd) ->
                combine_demodulation_proofs bag env goal ld rd :: acc)
         acc r_demod)
    [] l_demod
;;

let solve_demodulating bag env table initgoal steps =
  let proof,menv,eq,ty,left,right = open_goal initgoal in
  let uri = 
    match eq with
    | Cic.MutInd (u,_,_) -> u
    | _ -> assert false
  in
  let _, context, ugraph = env in
  let v1, bag, l_demod = demod_all steps bag env table ([],menv,left) in
  let v2, bag, r_demod = demod_all steps bag env table ([],menv,right) in
  let is_solved left right ml mr =
    let m = ml @ (List.filter 
      (fun (x,_,_) -> not (List.exists (fun (y,_,_) -> x=y)ml)) mr) 
    in
    try 
      let s,_,_ =
        Founif.unification [] m context left right CicUniv.empty_ugraph in
      Some (bag, m,s,Equality.Exact (Equality.refl_proof uri ty left))
    with CicUnification.UnificationFailure _ -> 
      let solutions = 
       unification_all env table (Equality.mk_tmp_equality 
          (0,(Cic.Implicit None,left,right,Utils.Incomparable),m))
      in
      if solutions = [] then None
      else
        let s, e, swapped = List.hd solutions in
        let _,p,(ty,l,r,_),me,id = Equality.open_equality e in 
        let bag, p = 
          if swapped then Equality.symmetric bag ty l id uri me else bag, p
        in
        Some (bag, m,s, p) 
  in
  let newgoal =  
   HExtlib.list_findopt
     (fun (pr,mr,r) _ ->
         try
           let pl,ml,l,bag,m,s,p = 
             match 
             HExtlib.list_findopt (fun (pl,ml,l) _ -> 
               match is_solved l r ml mr with
               | None -> None
               | Some (bag,m,s,p) -> Some (pl,ml,l,bag,m,s,p)
             ) l_demod
             with Some x -> x | _ -> raise Not_found
           in
           let pl = 
             List.map 
               (fun (rule,pos,id,subst,pred) -> 
                 let pred = 
                   match pred with
                   | Cic.Lambda (name,src,tgt) ->
                       Cic.Lambda (name,src, 
                         Cic.Appl[eq;ty;tgt;CicSubstitution.lift 1 right])
                   | _ -> assert false                 
                 in
                 rule,pos,id,subst,pred)
               pl
           in
           let pr = 
             List.map 
               (fun (rule,pos,id,subst,pred) -> 
                 let pred = 
                   match pred with
                   | Cic.Lambda (name,src,tgt) ->
                       Cic.Lambda (name,src, 
                         Cic.Appl[eq;ty;CicSubstitution.lift 1 l;tgt])
                   | _ -> assert false                 
                 in
                 rule,pos,id,subst,pred)
               pr
           in
           Some (bag,pr@pl@proof,m,s,p)
         with Not_found -> None)
     r_demod
  in
  newgoal
;;


 
