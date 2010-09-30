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

open ProofEngineTypes

(* Note: this code is almost identical to change_tac and
*  it could be unified by making the change function a callback *)
let reduction_tac ~reduction ~pattern (proof,goal) =
  let curi,metasenv,subst,pbo,pty, attrs = proof in
  let (metano,context,ty) as conjecture = CicUtil.lookup_meta goal metasenv in
  let change subst where terms metasenv ugraph =
   if terms = [] then where, metasenv, ugraph
   else
     let pairs, metasenv, ugraph =
       List.fold_left
        (fun (pairs, metasenv, ugraph) (context, t) ->
          let reduction, metasenv, ugraph = reduction context metasenv ugraph in
          ((t, reduction context t) :: pairs), metasenv, ugraph)
        ([], metasenv, ugraph)
        terms
     in
     let terms, terms' = List.split pairs in
     let where' =
       ProofEngineReduction.replace ~equality:(==) ~what:terms ~with_what:terms'
        ~where:where
     in
     CicMetaSubst.apply_subst subst where', metasenv, ugraph
  in
  let (subst,metasenv,ugraph,selected_context,selected_ty) =
    ProofEngineHelpers.select ~subst ~metasenv ~ugraph:CicUniv.oblivion_ugraph
      ~conjecture ~pattern
  in
  let ty', metasenv, ugraph = change subst ty selected_ty metasenv ugraph in
  let context', metasenv, ugraph =
   List.fold_right2
    (fun entry selected_entry (context', metasenv, ugraph) ->
      match entry,selected_entry with
         None,None -> None::context', metasenv, ugraph
       | Some (name,Cic.Decl ty),Some (`Decl selected_ty) ->
          let ty', metasenv, ugraph =
            change subst ty selected_ty metasenv ugraph
          in
          Some (name,Cic.Decl ty')::context', metasenv, ugraph
       | Some (name,Cic.Def (bo,ty)),Some (`Def (selected_bo,selected_ty)) ->
          let bo', metasenv, ugraph =
            change subst bo selected_bo metasenv ugraph in
          let ty', metasenv, ugraph =
            change subst ty selected_ty metasenv ugraph
          in
           (Some (name,Cic.Def (bo',ty'))::context'), metasenv, ugraph
       | _,_ -> assert false
    ) context selected_context ([], metasenv, ugraph) in
  let metasenv' = 
    List.map (function 
      | (n,_,_) when n = metano -> (metano,context',ty')
      | _ as t -> t
    ) metasenv
  in
  (curi,metasenv',subst,pbo,pty, attrs), [metano]
;;

let simpl_tac ~pattern =
 mk_tactic (reduction_tac
  ~reduction:(const_lazy_reduction ProofEngineReduction.simpl) ~pattern)

let unfold_tac what ~pattern =
  let reduction =
    match what with
    | None -> const_lazy_reduction (ProofEngineReduction.unfold ?what:None)
    | Some lazy_term ->
        (fun context metasenv ugraph ->
          let what, metasenv, ugraph = lazy_term context metasenv ugraph in
          let unfold ctx t =
           try
            ProofEngineReduction.unfold ~what ctx t
           with
            (* Not what we would like to have; however, this is required
               right now for the case of a definition in the context:
               if it works only in the body (or only in the type), that should
               be accepted *)
            ProofEngineTypes.Fail _ -> t
          in
          unfold, metasenv, ugraph)
  in
  mk_tactic (reduction_tac ~reduction ~pattern)
  
let whd_tac ~pattern =
 mk_tactic (reduction_tac
  ~reduction:(const_lazy_reduction CicReduction.whd) ~pattern)

let normalize_tac ~pattern =
 mk_tactic (reduction_tac
  ~reduction:(const_lazy_reduction CicReduction.normalize) ~pattern)

let head_beta_reduce_tac ?delta ?upto ~pattern =
 mk_tactic (reduction_tac
  ~reduction:
    (const_lazy_reduction
      (fun _context -> CicReduction.head_beta_reduce ?delta ?upto)) ~pattern)

exception NotConvertible

(* Note: this code is almost identical to reduction_tac and
*  it could be unified by making the change function a callback *)
(* CSC: with_what is parsed in the context of the goal, but it should replace
        something that lives in a completely different context. Thus we
        perform a delift + lift phase to move it in the right context. However,
        in this way the tactic is less powerful than expected: with_what cannot
        reference variables that are local to the term that is going to be
        replaced. To fix this we should parse with_what in the context of the
        term(s) to be replaced. *)
let change_tac ?(with_cast=false) ~pattern with_what  =
 let change_tac ~pattern ~with_what (proof, goal) =
  let curi,metasenv,subst,pbo,pty, attrs = proof in
  let (metano,context,ty) as conjecture = CicUtil.lookup_meta goal metasenv in
  let change subst where terms metasenv ugraph =
   if terms = [] then where, metasenv, ugraph
   else
    let pairs, metasenv, ugraph =
      List.fold_left
        (fun (pairs, metasenv, ugraph) (context_of_t, t) ->
          let with_what, metasenv, ugraph =
            with_what context_of_t metasenv ugraph
          in
          let _,u =
            CicTypeChecker.type_of_aux' 
              metasenv ~subst context_of_t with_what ugraph
          in
          let b,_ =
           CicReduction.are_convertible 
             ~metasenv ~subst context_of_t t with_what u
          in
          if b then
           ((t, with_what) :: pairs), metasenv, ugraph
          else
           raise NotConvertible)
        ([], metasenv, ugraph)
        terms
    in
    let terms, terms' = List.split pairs in
     let where' =
      ProofEngineReduction.replace ~equality:(==) ~what:terms ~with_what:terms'
       ~where:where
     in
      CicMetaSubst.apply_subst subst where', metasenv, ugraph
  in
  let (subst,metasenv,ugraph,selected_context,selected_ty) =
   ProofEngineHelpers.select 
     ~metasenv ~subst ~ugraph:CicUniv.oblivion_ugraph ~conjecture ~pattern 
  in
  let ty', metasenv, ugraph = change subst ty selected_ty metasenv ugraph in
  let context', metasenv, ugraph =
   List.fold_right2
    (fun entry selected_entry (context', metasenv, ugraph) ->
     match entry,selected_entry with
         None,None -> (None::context'), metasenv, ugraph
       | Some (name,Cic.Decl ty),Some (`Decl selected_ty) ->
          let ty', metasenv, ugraph =
            change subst ty selected_ty metasenv ugraph
          in
           (Some (name,Cic.Decl ty')::context'), metasenv, ugraph
       | Some (name,Cic.Def (bo,ty)),Some (`Def (selected_bo,selected_ty)) ->
          let bo', metasenv, ugraph =
            change subst bo selected_bo metasenv ugraph in
          let ty', metasenv, ugraph =
            change subst ty selected_ty metasenv ugraph
          in
           (Some (name,Cic.Def (bo',ty'))::context'), metasenv, ugraph
       | _,_ -> assert false
    ) context selected_context ([], metasenv, ugraph) in
  let metasenv' = 
    List.map
      (function 
        | (n,_,_) when n = metano -> (metano,context',ty')
        | _ as t -> t)
      metasenv
  in
   let proof,goal = (curi,metasenv',subst,pbo,pty, attrs), metano in
    if with_cast then
     let metano' = ProofEngineHelpers.new_meta_of_proof ~proof in
     let (newproof,_) =
       let irl= CicMkImplicit.identity_relocation_list_for_metavariable context'
       in
        ProofEngineHelpers.subst_meta_in_proof
         proof metano
          (Cic.Cast (Cic.Meta(metano',irl),ty')) [metano',context',ty']
     in
      newproof, [metano']
    else
     proof,[goal]
  in
    mk_tactic (change_tac ~pattern ~with_what)
;;

let fold_tac ~reduction ~term ~pattern =
 let fold_tac ~reduction ~term ~pattern:(wanted,hyps_pat,concl_pat) status =
  assert (wanted = None); (* this should be checked syntactically *)
  let reduced_term =
    (fun context metasenv ugraph ->
      let term, metasenv, ugraph = term context metasenv ugraph in
      let reduction, metasenv, ugraph = reduction context metasenv ugraph in
      reduction context term, metasenv, ugraph)
  in
   apply_tactic
    (change_tac ~pattern:(Some reduced_term,hyps_pat,concl_pat) term) status
 in
  mk_tactic (fold_tac ~reduction ~term ~pattern)
;;

