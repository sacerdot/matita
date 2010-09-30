(* Copyright (C) 2002, HELM Team.
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

module C    = Cic
module U    = UriManager
module PET  = ProofEngineTypes
module PER  = ProofEngineReduction
module PEH  = ProofEngineHelpers
module PESR = ProofEngineStructuralRules
module P    = PrimitiveTactics 
module T    = Tacticals 
module R    = CicReduction
module S    = CicSubstitution
module TC   = CicTypeChecker
module LO   = LibraryObjects
module DTI  = DoubleTypeInference
module HEL  = HExtlib

let rec rewrite ~direction ~pattern:(wanted,hyps_pat,concl_pat) equality status=
  assert (wanted = None);   (* this should be checked syntactically *)
  let proof,goal = status in
  let curi, metasenv, subst, pbo, pty, attrs = proof in
  let (metano,context,gty) = CicUtil.lookup_meta goal metasenv in
  match hyps_pat with
     he::(_::_ as tl) ->
      PET.apply_tactic
        (T.then_
          (PET.mk_tactic (rewrite ~direction
             ~pattern:(None,[he],None) equality))
          (PET.mk_tactic (rewrite ~direction 
             ~pattern:(None,tl,concl_pat) (S.lift 1 equality)))
        ) status
   | [_] as hyps_pat when concl_pat <> None ->
      PET.apply_tactic
        (T.then_
          (PET.mk_tactic (rewrite ~direction
           ~pattern:(None,hyps_pat,None) equality))
          (PET.mk_tactic (rewrite ~direction 
           ~pattern:(None,[],concl_pat) (S.lift 1 equality)))
        ) status
   | _ ->
  let arg,dir2,tac,concl_pat,gty =
   match hyps_pat with
      [] -> None,true,(fun ~term _ -> P.exact_tac term),concl_pat,gty
    | [name,pat] ->
       let arg,gty = ProofEngineHelpers.find_hyp name context in
       let dummy = "dummy" in
        Some arg,false,
         (fun ~term typ ->
           T.seq
            ~tactics:
              [PESR.rename [name] [dummy];
               P.letin_tac
                ~mk_fresh_name_callback:(fun _ _ _ ~typ -> Cic.Name name) term;
               PESR.clearbody name;
	       ReductionTactics.change_tac
                ~pattern:
                  (None,[name,Cic.Implicit (Some `Hole)], None)
                (ProofEngineTypes.const_lazy_term typ);
               PESR.clear [dummy]
              ]),
         Some pat,gty
    | _::_ -> assert false
  in
  let gsort,_ =
   CicTypeChecker.type_of_aux' 
     metasenv ~subst context gty CicUniv.oblivion_ugraph 
  in
  let if_right_to_left do_not_change a b = 
    match direction with
    | `RightToLeft -> if do_not_change then a else b
    | `LeftToRight -> if do_not_change then b else a
  in
  let ty_eq,ugraph = 
    CicTypeChecker.type_of_aux' metasenv ~subst context equality 
      CicUniv.oblivion_ugraph in 
  let (ty_eq,metasenv',arguments,fresh_meta) =
   TermUtil.saturate_term
    (ProofEngineHelpers.new_meta_of_proof proof) metasenv context ty_eq 0 in  
  let equality =
   if List.length arguments = 0 then
    equality
   else
    C.Appl (equality :: arguments) in
  (* t1x is t2 if we are rewriting in an hypothesis *)
  let eq_ind, ty, t1, t2, t1x =
    match ty_eq with
    | C.Appl [C.MutInd (uri, 0, []); ty; t1; t2]
      when LibraryObjects.is_eq_URI uri ->
        let ind_uri =
         match gsort with
            C.Sort C.Prop ->
             if_right_to_left dir2
              LibraryObjects.eq_ind_URI LibraryObjects.eq_ind_r_URI
          | C.Sort C.Set ->
             if_right_to_left dir2
              LibraryObjects.eq_rec_URI LibraryObjects.eq_rec_r_URI
          | _ ->
             if_right_to_left dir2
              LibraryObjects.eq_rect_URI LibraryObjects.eq_rect_r_URI
        in
        let eq_ind = C.Const (ind_uri uri,[]) in
         if dir2 then
          if_right_to_left true (eq_ind,ty,t2,t1,t2) (eq_ind,ty,t1,t2,t1)
         else
          if_right_to_left true (eq_ind,ty,t1,t2,t2) (eq_ind,ty,t2,t1,t1)
    | _ -> raise (PET.Fail (lazy "Rewrite: argument is not a proof of an equality")) in
  (* now we always do as if direction was `LeftToRight *)
  let fresh_name = 
    FreshNamesGenerator.mk_fresh_name 
    ~subst metasenv' context C.Anonymous ~typ:ty in
  let lifted_t1 = S.lift 1 t1x in
  let lifted_gty = S.lift 1 gty in
  let lifted_conjecture =
    metano,(Some (fresh_name,Cic.Decl ty))::context,lifted_gty in
  let lifted_pattern =
    let lifted_concl_pat =
      match concl_pat with
      | None -> None
      | Some term -> Some (S.lift 1 term) in
    Some (fun c m u -> 
       let distance  = pred (List.length c - List.length context) in
       S.lift distance lifted_t1, m, u),[],lifted_concl_pat
  in
  let subst,metasenv',ugraph,_,selected_terms_with_context =
   ProofEngineHelpers.select
    ~metasenv:metasenv' ~subst ~ugraph ~conjecture:lifted_conjecture
     ~pattern:lifted_pattern in
  let metasenv' = CicMetaSubst.apply_subst_metasenv subst metasenv' in  
  let what,with_what = 
   (* Note: Rel 1 does not live in the context context_of_t           *)
   (* The replace_lifting_csc 0 function will take care of lifting it *)
   (* to context_of_t                                                 *)
   List.fold_right
    (fun (context_of_t,t) (l1,l2) -> t::l1, Cic.Rel 1::l2)
    selected_terms_with_context ([],[]) in
  let t1 = CicMetaSubst.apply_subst subst t1 in
  let t2 = CicMetaSubst.apply_subst subst t2 in
  let ty = CicMetaSubst.apply_subst subst ty in
  let pbo = lazy (CicMetaSubst.apply_subst subst (Lazy.force pbo)) in
  let pty = CicMetaSubst.apply_subst subst pty in
  let equality = CicMetaSubst.apply_subst subst equality in
  let abstr_gty =
   ProofEngineReduction.replace_lifting_csc 0
    ~equality:(==) ~what ~with_what:with_what ~where:lifted_gty in
  if lifted_gty = abstr_gty then 
    raise (ProofEngineTypes.Fail (lazy "nothing to do"));
  let abstr_gty = CicMetaSubst.apply_subst subst abstr_gty in
  let pred = C.Lambda (fresh_name, ty, abstr_gty) in
  (* The argument is either a meta if we are rewriting in the conclusion
     or the hypothesis if we are rewriting in an hypothesis *)
  let metasenv',arg,newtyp =
   match arg with
      None ->
       let fresh_meta = CicMkImplicit.new_meta metasenv' subst in
       let gty' = S.subst t2 abstr_gty in
       let irl =
        CicMkImplicit.identity_relocation_list_for_metavariable context in
       let metasenv' = (fresh_meta,context,gty')::metasenv' in
        metasenv', C.Meta (fresh_meta,irl), Cic.Rel (-1) (* dummy term, never used *)
    | Some arg ->
       let gty' = S.subst t1 abstr_gty in
        metasenv',arg,gty'
  in
  let exact_proof = 
    C.Appl [eq_ind ; ty ; t2 ; pred ; arg ; t1 ;equality]
  in
  try 
    let (proof',goals) =
      PET.apply_tactic (tac ~term:exact_proof newtyp) 
        ((curi,metasenv',subst,pbo,pty, attrs),goal)
    in
    let goals =
     goals@(ProofEngineHelpers.compare_metasenvs ~oldmetasenv:metasenv
      ~newmetasenv:metasenv')
    in
     (proof',goals)
  with (* FG: this should be PET.Fail _ *)
     TC.TypeCheckerFailure m -> 
      let msg = lazy ("rewrite: "^ Lazy.force m) in
      raise (PET.Fail msg)
;;

let rewrite_tac ~direction ~pattern equality names =
   let _, hyps_pat, _ = pattern in 
   let froms = List.map fst hyps_pat in
   let start = PET.mk_tactic (rewrite ~direction ~pattern equality) in
   let continuation = PESR.rename ~froms ~tos:names in
   if names = [] then start else T.then_ ~start ~continuation
;;

let rewrite_simpl_tac ~direction ~pattern equality names =
  T.then_ 
   ~start:(rewrite_tac ~direction ~pattern equality names)
   ~continuation:
     (ReductionTactics.simpl_tac
       ~pattern:(ProofEngineTypes.conclusion_pattern None))

let replace_tac ~(pattern: ProofEngineTypes.lazy_pattern) ~with_what =
 let replace_tac ~(pattern: ProofEngineTypes.lazy_pattern) ~with_what status =
  let _wanted, hyps_pat, concl_pat = pattern in
  let (proof, goal) = status in
  let uri,metasenv,subst,pbo,pty, attrs = proof in
  let (_,context,ty) as conjecture = CicUtil.lookup_meta goal metasenv in
  assert (hyps_pat = []); (*CSC: not implemented yet *)
  let eq_URI =
   match LibraryObjects.eq_URI () with
      Some uri -> uri
    | None -> raise (ProofEngineTypes.Fail (lazy "You need to register the default equality first. Please use the \"default\" command"))
  in
  let context_len = List.length context in
  let subst,metasenv,u,_,selected_terms_with_context =
   ProofEngineHelpers.select ~subst ~metasenv ~ugraph:CicUniv.oblivion_ugraph
    ~conjecture ~pattern in
  let metasenv = CicMetaSubst.apply_subst_metasenv subst metasenv in
  let with_what, metasenv, u = with_what context metasenv u in
  let with_what = CicMetaSubst.apply_subst subst with_what in
  let pbo = lazy (CicMetaSubst.apply_subst subst (Lazy.force pbo)) in
  let pty = CicMetaSubst.apply_subst subst pty in
  let status = (uri,metasenv,subst,pbo,pty, attrs),goal in
  let ty_of_with_what,u =
   CicTypeChecker.type_of_aux'
    metasenv ~subst context with_what CicUniv.oblivion_ugraph in
  let whats =
   match selected_terms_with_context with
      [] -> raise (ProofEngineTypes.Fail (lazy "Replace: no term selected"))
    | l ->
      List.map
       (fun (context_of_t,t) ->
         let t_in_context =
          try
           let context_of_t_len = List.length context_of_t in
           if context_of_t_len = context_len then t
           else
            (let t_in_context,subst,metasenv' =
              CicMetaSubst.delift_rels [] metasenv
               (context_of_t_len - context_len) t
             in
              assert (subst = []);
              assert (metasenv = metasenv');
              t_in_context)
          with
           CicMetaSubst.DeliftingARelWouldCaptureAFreeVariable ->
            (*CSC: we could implement something stronger by completely changing
              the semantics of the tactic *)
            raise (ProofEngineTypes.Fail
             (lazy "Replace: one of the selected terms is not closed")) in
         let ty_of_t_in_context,u = (* TASSI: FIXME *)
          CicTypeChecker.type_of_aux' metasenv ~subst context t_in_context
           CicUniv.oblivion_ugraph in
         let b,u = CicReduction.are_convertible ~metasenv ~subst context
          ty_of_with_what ty_of_t_in_context u in
         if b then
          let concl_pat_for_t = ProofEngineHelpers.pattern_of ~term:ty [t] in
          let pattern_for_t = None,[],Some concl_pat_for_t in
           t_in_context,pattern_for_t
         else
          raise
           (ProofEngineTypes.Fail
             (lazy "Replace: one of the selected terms and the term to be replaced with have not convertible types"))
       ) l in
  let rec aux n whats (status : ProofEngineTypes.status) =
   match whats with
      [] -> ProofEngineTypes.apply_tactic T.id_tac status
    | (what,lazy_pattern)::tl ->
       let what = S.lift n what in
       let with_what = S.lift n with_what in
       let ty_of_with_what = S.lift n ty_of_with_what in
       ProofEngineTypes.apply_tactic
         (T.thens
            ~start:(
              P.cut_tac 
               (C.Appl [
                 (C.MutInd (eq_URI, 0, [])) ;
                 ty_of_with_what ; 
                 what ; 
                 with_what]))
            ~continuations:[            
              T.then_
                ~start:(
                  rewrite_tac 
                    ~direction:`LeftToRight ~pattern:lazy_pattern (C.Rel 1) [])
                 ~continuation:(
                   T.then_
                    ~start:(
                      ProofEngineTypes.mk_tactic
                       (function ((proof,goal) as status) ->
                         let _,metasenv,_,_,_, _ = proof in
                         let _,context,_ = CicUtil.lookup_meta goal metasenv in
                         let hyps =
                          try
                           match List.hd context with
                              Some (Cic.Name name,_) -> [name]
                            | _ -> assert false
                          with (Failure "hd") -> assert false
                         in
                          ProofEngineTypes.apply_tactic
                           (PESR.clear ~hyps) status))
                    ~continuation:(aux_tac (n + 1) tl));
              T.id_tac])
         status
  and aux_tac n tl = ProofEngineTypes.mk_tactic (aux n tl) in
   aux 0 whats (status : ProofEngineTypes.status)
 in
   ProofEngineTypes.mk_tactic (replace_tac ~pattern ~with_what)
;;


(* All these tacs do is applying the right constructor/theorem *)

let reflexivity_tac =
  IntroductionTactics.constructor_tac ~n:1
;;

let symmetry_tac =
 let symmetry_tac (proof, goal) =
   let (_,metasenv,_,_,_, _) = proof in
    let metano,context,ty = CicUtil.lookup_meta goal metasenv in
     match (R.whd context ty) with
        (C.Appl [(C.MutInd (uri, 0, [])); _; _; _])
	 when LibraryObjects.is_eq_URI uri ->
	  ProofEngineTypes.apply_tactic 
           (PrimitiveTactics.apply_tac 
	    ~term:(C.Const (LibraryObjects.sym_eq_URI uri, []))) 
	   (proof,goal)

      | _ -> raise (ProofEngineTypes.Fail (lazy "Symmetry failed"))
 in
  ProofEngineTypes.mk_tactic symmetry_tac
;;

let transitivity_tac ~term =
 let transitivity_tac ~term status =
  let (proof, goal) = status in
   let (_,metasenv,_,_,_, _) = proof in
    let metano,context,ty = CicUtil.lookup_meta goal metasenv in
     match (R.whd context ty) with
        (C.Appl [(C.MutInd (uri, 0, [])); _; _; _]) 
	when LibraryObjects.is_eq_URI uri ->
         ProofEngineTypes.apply_tactic 
	 (T.thens
          ~start:(PrimitiveTactics.apply_tac
            ~term: (C.Const (LibraryObjects.trans_eq_URI uri, [])))
          ~continuations:
            [PrimitiveTactics.exact_tac ~term ; T.id_tac ; T.id_tac])
          status

      | _ -> raise (ProofEngineTypes.Fail (lazy "Transitivity failed"))
 in
  ProofEngineTypes.mk_tactic (transitivity_tac ~term)
;;

