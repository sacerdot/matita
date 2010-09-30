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

(******************************************************************************)
(*                                                                            *)
(*                               PROJECT HELM                                 *)
(*                                                                            *)
(*                Claudio Sacerdoti Coen <sacerdot@cs.unibo.it>               *)
(*                                 12/04/2002                                 *)
(*                                                                            *)
(*                                                                            *)
(******************************************************************************)

(* $Id$ *)

(* The code of this module is derived from the code of CicReduction *)

exception Impossible of int;;
exception ReferenceToConstant;;
exception ReferenceToVariable;;
exception ReferenceToCurrentProof;;
exception ReferenceToInductiveDefinition;;
exception WrongUriToInductiveDefinition;;
exception WrongUriToConstant;;
exception RelToHiddenHypothesis;;

module C = Cic
module S = CicSubstitution

let debug = false
let prerr_endline =
  if debug then prerr_endline else (fun x -> ())
;;

exception WhatAndWithWhatDoNotHaveTheSameLength;;

(* Replaces "textually" in "where" every term in "what" with the corresponding
   term in "with_what". The terms in "what" ARE NOT lifted when binders are
   crossed. The terms in "with_what" ARE NOT lifted when binders are crossed.
   Every free variable in "where" IS NOT lifted by nnn.
*)
let replace ~equality ~what ~with_what ~where =
  let find_image t =
   let rec find_image_aux =
    function
       [],[] -> raise Not_found
     | what::tl1,with_what::tl2 ->
        if equality what t then with_what else find_image_aux (tl1,tl2)
     | _,_ -> raise WhatAndWithWhatDoNotHaveTheSameLength
   in
    find_image_aux (what,with_what)
  in
  let rec aux t =
   try
    find_image t
   with Not_found ->
    match t with
       C.Rel _ -> t
     | C.Var (uri,exp_named_subst) ->
        C.Var (uri,List.map (function (uri,t) -> uri, aux t) exp_named_subst)
     | C.Meta _ -> t
     | C.Sort _ -> t
     | C.Implicit _ as t -> t
     | C.Cast (te,ty) -> C.Cast (aux te, aux ty)
     | C.Prod (n,s,t) -> C.Prod (n, aux s, aux t)
     | C.Lambda (n,s,t) -> C.Lambda (n, aux s, aux t)
     | C.LetIn (n,s,ty,t) -> C.LetIn (n, aux s, aux ty, aux t)
     | C.Appl l ->
        (* Invariant enforced: no application of an application *)
        (match List.map aux l with
            (C.Appl l')::tl -> C.Appl (l'@tl)
          | l' -> C.Appl l')
     | C.Const (uri,exp_named_subst) ->
        C.Const (uri,List.map (function (uri,t) -> uri, aux t) exp_named_subst)
     | C.MutInd (uri,i,exp_named_subst) ->
        C.MutInd
         (uri,i,List.map (function (uri,t) -> uri, aux t) exp_named_subst)
     | C.MutConstruct (uri,i,j,exp_named_subst) ->
        C.MutConstruct
         (uri,i,j,List.map (function (uri,t) -> uri, aux t) exp_named_subst)
     | C.MutCase (sp,i,outt,t,pl) ->
        C.MutCase (sp,i,aux outt, aux t,List.map aux pl)
     | C.Fix (i,fl) ->
        let substitutedfl =
         List.map
          (fun (name,i,ty,bo) -> (name, i, aux ty, aux bo))
           fl
        in
         C.Fix (i, substitutedfl)
     | C.CoFix (i,fl) ->
        let substitutedfl =
         List.map
          (fun (name,ty,bo) -> (name, aux ty, aux bo))
           fl
        in
         C.CoFix (i, substitutedfl)
   in
    aux where
;;

(* Replaces in "where" every term in "what" with the corresponding
   term in "with_what". The terms in "what" ARE lifted when binders are
   crossed. The terms in "with_what" ARE lifted when binders are crossed.
   Every free variable in "where" IS NOT lifted by nnn.
   Thus "replace_lifting_csc 1 ~with_what:[Rel 1; ... ; Rel 1]" is the
   inverse of subst up to the fact that free variables in "where" are NOT
   lifted.  *)
let replace_lifting ~equality ~context ~what ~with_what ~where =
  let find_image ctx what t =
   let rec find_image_aux =
    function
       [],[] -> raise Not_found
     | what::tl1,with_what::tl2 ->
        if equality ctx what t then with_what else find_image_aux (tl1,tl2)
     | _,_ -> raise WhatAndWithWhatDoNotHaveTheSameLength
   in
    find_image_aux (what,with_what)
  in
  let add_ctx ctx n s = (Some (n, Cic.Decl s))::ctx in
  let add_ctx1 ctx n s ty = (Some (n, Cic.Def (s,ty)))::ctx in
  let rec substaux k ctx what t =
   try
    S.lift (k-1) (find_image ctx what t)
   with Not_found ->
    match t with
      C.Rel n as t -> t
    | C.Var (uri,exp_named_subst) ->
       let exp_named_subst' =
        List.map (function (uri,t) -> uri,substaux k ctx what t) exp_named_subst
       in
        C.Var (uri,exp_named_subst')
    | C.Meta (i, l) -> 
       let l' =
        List.map
         (function
             None -> None
           | Some t -> Some (substaux k ctx what t)
         ) l
       in
        C.Meta(i,l')
    | C.Sort _ as t -> t
    | C.Implicit _ as t -> t
    | C.Cast (te,ty) -> C.Cast (substaux k ctx what te, substaux k ctx what ty)
    | C.Prod (n,s,t) ->
       C.Prod
        (n, substaux k ctx what s, substaux (k + 1) (add_ctx ctx n s) (List.map (S.lift 1) what) t)
    | C.Lambda (n,s,t) ->
       C.Lambda
        (n, substaux k ctx what s, substaux (k + 1) (add_ctx ctx n s) (List.map (S.lift 1) what) t)
    | C.LetIn (n,s,ty,t) ->
       C.LetIn
        (n, substaux k ctx what s, substaux k ctx what ty, substaux (k + 1) (add_ctx1 ctx n s ty) (List.map (S.lift 1) what) t)
    | C.Appl (he::tl) ->
       (* Invariant: no Appl applied to another Appl *)
       let tl' = List.map (substaux k ctx what) tl in
        begin
         match substaux k ctx what he with
            C.Appl l -> C.Appl (l@tl')
          | _ as he' -> C.Appl (he'::tl')
        end
    | C.Appl _ -> assert false
    | C.Const (uri,exp_named_subst) ->
       let exp_named_subst' =
        List.map (function (uri,t) -> uri,substaux k ctx what t) exp_named_subst
       in
       C.Const (uri,exp_named_subst')
    | C.MutInd (uri,i,exp_named_subst) ->
       let exp_named_subst' =
        List.map (function (uri,t) -> uri,substaux k ctx what t) exp_named_subst
       in
        C.MutInd (uri,i,exp_named_subst')
    | C.MutConstruct (uri,i,j,exp_named_subst) ->
       let exp_named_subst' =
        List.map (function (uri,t) -> uri,substaux k ctx what t) exp_named_subst
       in
        C.MutConstruct (uri,i,j,exp_named_subst')
    | C.MutCase (sp,i,outt,t,pl) ->
       C.MutCase (sp,i,substaux k ctx what outt, substaux k ctx what t,
        List.map (substaux k ctx what) pl)
    | C.Fix (i,fl) ->
       let len = List.length fl in
       let substitutedfl =
        List.map
         (fun (name,i,ty,bo) -> (* WRONG CTX *)
           (name, i, substaux k ctx what ty,
             substaux (k+len) ctx (List.map (S.lift len) what) bo)
         ) fl
       in
        C.Fix (i, substitutedfl)
    | C.CoFix (i,fl) ->
       let len = List.length fl in
       let substitutedfl =
        List.map
         (fun (name,ty,bo) -> (* WRONG CTX *)
           (name, substaux k ctx what ty,
             substaux (k+len) ctx (List.map (S.lift len) what) bo)
         ) fl
       in
        C.CoFix (i, substitutedfl)
 in
  substaux 1 context what where
;;

(* Replaces in "where" every term in "what" with the corresponding
   term in "with_what". The terms in "what" ARE NOT lifted when binders are
   crossed. The terms in "with_what" ARE lifted when binders are crossed.
   Every free variable in "where" IS lifted by nnn.
   Thus "replace_lifting_csc 1 ~with_what:[Rel 1; ... ; Rel 1]" is the
   inverse of subst up to the fact that "what" terms are NOT lifted. *)
let replace_lifting_csc nnn ~equality ~what ~with_what ~where =
  let find_image t =
   let rec find_image_aux =
    function
       [],[] -> raise Not_found
     | what::tl1,with_what::tl2 ->
         if equality what t then with_what else find_image_aux (tl1,tl2)
     | _,_ -> raise WhatAndWithWhatDoNotHaveTheSameLength
   in
    find_image_aux (what,with_what)
  in
  let rec substaux k t =
   try
    S.lift (k-1) (find_image t)
   with Not_found ->
    match t with
       C.Rel n ->
        if n < k then C.Rel n else C.Rel (n + nnn)
     | C.Var (uri,exp_named_subst) ->
        let exp_named_subst' =
         List.map (function (uri,t) -> uri,substaux k t) exp_named_subst
        in
         C.Var (uri,exp_named_subst')
     | C.Meta (i, l) -> 
        let l' =
         List.map
          (function
              None -> None
            | Some t -> Some (substaux k t)
          ) l
        in
         C.Meta(i,l')
     | C.Sort _ as t -> t
     | C.Implicit _ as t -> t
     | C.Cast (te,ty) -> C.Cast (substaux k te, substaux k ty)
     | C.Prod (n,s,t) ->
        C.Prod (n, substaux k s, substaux (k + 1) t)
     | C.Lambda (n,s,t) ->
        C.Lambda (n, substaux k s, substaux (k + 1) t)
     | C.LetIn (n,s,ty,t) ->
        C.LetIn (n, substaux k s, substaux k ty, substaux (k + 1) t)
     | C.Appl (he::tl) ->
        (* Invariant: no Appl applied to another Appl *)
        let tl' = List.map (substaux k) tl in
         begin
          match substaux k he with
             C.Appl l -> C.Appl (l@tl')
           | _ as he' -> C.Appl (he'::tl')
         end
     | C.Appl _ -> assert false
     | C.Const (uri,exp_named_subst) ->
        let exp_named_subst' =
         List.map (function (uri,t) -> uri,substaux k t) exp_named_subst
        in
        C.Const (uri,exp_named_subst')
     | C.MutInd (uri,i,exp_named_subst) ->
        let exp_named_subst' =
         List.map (function (uri,t) -> uri,substaux k t) exp_named_subst
        in
         C.MutInd (uri,i,exp_named_subst')
     | C.MutConstruct (uri,i,j,exp_named_subst) ->
        let exp_named_subst' =
         List.map (function (uri,t) -> uri,substaux k t) exp_named_subst
        in
         C.MutConstruct (uri,i,j,exp_named_subst')
     | C.MutCase (sp,i,outt,t,pl) ->
        C.MutCase (sp,i,substaux k outt, substaux k t,
         List.map (substaux k) pl)
     | C.Fix (i,fl) ->
        let len = List.length fl in
        let substitutedfl =
         List.map
          (fun (name,i,ty,bo) ->
            (name, i, substaux k ty, substaux (k+len) bo))
           fl
        in
         C.Fix (i, substitutedfl)
     | C.CoFix (i,fl) ->
        let len = List.length fl in
        let substitutedfl =
         List.map
          (fun (name,ty,bo) ->
            (name, substaux k ty, substaux (k+len) bo))
           fl
        in
         C.CoFix (i, substitutedfl)
 in
  substaux 1 where
;;

(* This is like "replace_lifting_csc 1 ~with_what:[Rel 1; ... ; Rel 1]"
   up to the fact that the index to start from can be specified *)
let replace_with_rel_1_from ~equality ~what =
   let rec find_image t = function
      | []       -> false
      | hd :: tl -> equality t hd || find_image t tl 
   in
   let rec subst_term k t =
      if find_image t what then C.Rel k else inspect_term k t
   and inspect_term k = function
      | C.Rel i -> if i < k then C.Rel i else C.Rel (succ i)
      | C.Sort _ as t -> t
      | C.Implicit _ as t -> t
      | C.Var (uri, enss) ->
         let enss = List.map (subst_ens k) enss in
         C.Var (uri, enss)
      | C.Const (uri ,enss) ->
         let enss = List.map (subst_ens k) enss in
         C.Const (uri, enss)
     | C.MutInd (uri, tyno, enss) ->
         let enss = List.map (subst_ens k) enss in
         C.MutInd (uri, tyno, enss)
     | C.MutConstruct (uri, tyno, consno, enss) ->
         let enss = List.map (subst_ens k) enss in
         C.MutConstruct (uri, tyno, consno, enss)
     | C.Meta (i, mss) -> 
         let mss = List.map (subst_ms k) mss in
         C.Meta(i, mss)
     | C.Cast (t, v) -> C.Cast (subst_term k t, subst_term k v)
     | C.Appl ts ->      
         let ts = List.map (subst_term k) ts in
         C.Appl ts
     | C.MutCase (uri, tyno, outty, t, cases) ->
         let cases = List.map (subst_term k) cases in
	 C.MutCase (uri, tyno, subst_term k outty, subst_term k t, cases)
     | C.Prod (n, v, t) ->
        C.Prod (n, subst_term k v, subst_term (succ k) t)
     | C.Lambda (n, v, t) ->
        C.Lambda (n, subst_term k v, subst_term (succ k) t)
     | C.LetIn (n, v, ty, t) ->
        C.LetIn (n, subst_term k v, subst_term k ty, subst_term (succ k) t)
     | C.Fix (i, fixes) ->
        let fixesno = List.length fixes in
        let fixes = List.map (subst_fix fixesno k) fixes in
        C.Fix (i, fixes)
     | C.CoFix (i, cofixes) ->
        let cofixesno = List.length cofixes in
        let cofixes = List.map (subst_cofix cofixesno k) cofixes in
         C.CoFix (i, cofixes)
   and subst_ens k (uri, t) = uri, subst_term k t   
   and subst_ms k = function
      | None   -> None
      | Some t -> Some (subst_term k t)
   and subst_fix fixesno k (n, ind, ty, bo) =
      n, ind, subst_term k ty, subst_term (k + fixesno) bo
   and subst_cofix cofixesno k (n, ty, bo) =
      n, subst_term k ty, subst_term (k + cofixesno) bo
in
subst_term
   
let unfold ?what context where =
 let contextlen = List.length context in
 let first_is_the_expandable_head_of_second context' t1 t2 =
  match t1,t2 with
     Cic.Const (uri,_), Cic.Const (uri',_)
   | Cic.Var (uri,_), Cic.Var (uri',_)
   | Cic.Const (uri,_), Cic.Appl (Cic.Const (uri',_)::_)
   | Cic.Var (uri,_), Cic.Appl (Cic.Var (uri',_)::_) -> UriManager.eq uri uri'
   | Cic.Const _, _
   | Cic.Var _, _ -> false
   | Cic.Rel n, Cic.Rel m
   | Cic.Rel n, Cic.Appl (Cic.Rel m::_) ->
      n + (List.length context' - contextlen) = m
   | Cic.Rel _, _ -> false
   | _,_ ->
     raise
      (ProofEngineTypes.Fail
        (lazy "The term to unfold is not a constant, a variable or a bound variable "))
 in
 let appl he tl =
  if tl = [] then he else Cic.Appl (he::tl) in
 let cannot_delta_expand t =
  raise
   (ProofEngineTypes.Fail
     (lazy ("The term " ^ CicPp.ppterm t ^ " cannot be delta-expanded"))) in
 let rec hd_delta_beta context tl =
  function
    Cic.Rel n as t ->
     (try
       match List.nth context (n-1) with
          Some (_,Cic.Decl _) -> cannot_delta_expand t
        | Some (_,Cic.Def (bo,_)) ->
           CicReduction.head_beta_reduce
            (appl (CicSubstitution.lift n bo) tl)
        | None -> raise RelToHiddenHypothesis
      with
         Failure _ -> assert false)
  | Cic.Const (uri,exp_named_subst) as t ->
     let o,_ = CicEnvironment.get_obj CicUniv.oblivion_ugraph uri in
      (match o with
          Cic.Constant (_,Some body,_,_,_) ->
           CicReduction.head_beta_reduce
            (appl (CicSubstitution.subst_vars exp_named_subst body) tl)
        | Cic.Constant (_,None,_,_,_) -> cannot_delta_expand t
        | Cic.Variable _ -> raise ReferenceToVariable
        | Cic.CurrentProof _ -> raise ReferenceToCurrentProof
        | Cic.InductiveDefinition _ -> raise ReferenceToInductiveDefinition
      )
  | Cic.Var (uri,exp_named_subst) as t ->
     let o,_ = CicEnvironment.get_obj CicUniv.oblivion_ugraph uri in
      (match o with
          Cic.Constant _ -> raise ReferenceToConstant
        | Cic.CurrentProof _ -> raise ReferenceToCurrentProof
        | Cic.InductiveDefinition _ -> raise ReferenceToInductiveDefinition
        | Cic.Variable (_,Some body,_,_,_) ->
           CicReduction.head_beta_reduce
            (appl (CicSubstitution.subst_vars exp_named_subst body) tl)
        | Cic.Variable (_,None,_,_,_) -> cannot_delta_expand t
      )
   | Cic.Appl [] -> assert false
   | Cic.Appl (he::tl) -> hd_delta_beta context tl he
   | t -> cannot_delta_expand t
 in
 let context_and_matched_term_list =
  match what with
     None -> [context, where]
   | Some what ->
      let res =
       ProofEngineHelpers.locate_in_term
        ~equality:first_is_the_expandable_head_of_second
        what ~where context
      in
       if res = [] then
        raise
         (ProofEngineTypes.Fail
           (lazy ("Term "^ CicPp.ppterm what ^ " not found in " ^ CicPp.ppterm where)))
       else
        res
 in
  let reduced_terms =
   List.map
    (function (context,where) -> hd_delta_beta context [] where)
    context_and_matched_term_list in
  let whats = List.map snd context_and_matched_term_list in
   replace ~equality:(==) ~what:whats ~with_what:reduced_terms ~where
;;

exception WrongShape;;
exception AlreadySimplified;;

(* Takes a well-typed term and                                               *)
(*  1) Performs beta-iota-zeta reduction until delta reduction is needed     *)
(*  2) Attempts delta-reduction. If the residual is a Fix lambda-abstracted  *)
(*     w.r.t. zero or more variables and if the Fix can be reductaed, than it*)
(*     is reduced, the delta-reduction is succesfull and the whole algorithm *)
(*     is applied again to the new redex; Step 3.1) is applied to the result *)
(*     of the recursive simplification. Otherwise, if the Fix can not be     *)
(*     reduced, than the delta-reductions fails and the delta-redex is       *)
(*     not reduced. Otherwise, if the delta-residual is not the              *)
(*     lambda-abstraction of a Fix, then it performs step 3.2).              *)
(* 3.1) Folds the application of the constant to the arguments that did not  *)
(*     change in every iteration, i.e. to the actual arguments for the       *)
(*     lambda-abstractions that precede the Fix.                             *)
(* 3.2) Computes the head beta-zeta normal form of the term. Then it tries   *)
(*     reductions. If the reduction cannot be performed, it returns the      *)
(*     original term (not the head beta-zeta normal form of the definiendum) *)
(*CSC: It does not perform simplification in a Case *)

let simpl context =
 (* a simplified term is active if it can create a redex when used as an *)
 (* actual parameter                                                     *)
 let rec is_active =
  function
     C.Lambda _
   | C.MutConstruct _
   | C.Appl (C.MutConstruct _::_)
   | C.CoFix _ -> true
   | C.Cast (bo,_) -> is_active bo
   | C.LetIn _ -> assert false
   | _ -> false
 in
 (* reduceaux is equal to the reduceaux locally defined inside *)
 (* reduce, but for the const case.                            *) 
 (**** Step 1 ****)
 let rec reduceaux context l =
   function
      C.Rel n as t ->
       (* we never perform delta expansion automatically *)
       if l = [] then t else C.Appl (t::l)
    | C.Var (uri,exp_named_subst) ->
       let exp_named_subst' =
        reduceaux_exp_named_subst context l exp_named_subst
       in
        (let o,_ = CicEnvironment.get_obj CicUniv.oblivion_ugraph uri in
	  match o with
            C.Constant _ -> raise ReferenceToConstant
          | C.CurrentProof _ -> raise ReferenceToCurrentProof
          | C.InductiveDefinition _ -> raise ReferenceToInductiveDefinition
          | C.Variable (_,None,_,_,_) ->
            let t' = C.Var (uri,exp_named_subst') in
             if l = [] then t' else C.Appl (t'::l)
          | C.Variable (_,Some body,_,_,_) ->
             reduceaux context l
              (CicSubstitution.subst_vars exp_named_subst' body)
        )
    | C.Meta _ as t -> if l = [] then t else C.Appl (t::l)
    | C.Sort _ as t -> t (* l should be empty *)
    | C.Implicit _ as t -> t
    | C.Cast (te,ty) ->
       C.Cast (reduceaux context l te, reduceaux context [] ty)
    | C.Prod (name,s,t) ->
       assert (l = []) ;
       C.Prod (name,
        reduceaux context [] s,
        reduceaux ((Some (name,C.Decl s))::context) [] t)
    | C.Lambda (name,s,t) ->
       (match l with
           [] ->
            C.Lambda (name,
             reduceaux context [] s,
             reduceaux ((Some (name,C.Decl s))::context) [] t)
         | he::tl -> reduceaux context tl (S.subst he t)
           (* when name is Anonimous the substitution should be superfluous *)
       )
    | C.LetIn (n,s,ty,t) ->
       reduceaux context l (S.subst (reduceaux context [] s) t)
    | C.Appl (he::tl) ->
       let tl' = List.map (reduceaux context []) tl in
        reduceaux context (tl'@l) he
    | C.Appl [] -> raise (Impossible 1)
    | C.Const (uri,exp_named_subst) ->
       let exp_named_subst' =
        reduceaux_exp_named_subst context l exp_named_subst
       in
        (let o,_ = CicEnvironment.get_obj CicUniv.oblivion_ugraph uri in
	  match o with
           C.Constant (_,Some body,_,_,_) ->
            if List.exists is_active l then
             try_delta_expansion context l
              (C.Const (uri,exp_named_subst'))
              (CicSubstitution.subst_vars exp_named_subst' body)
            else
             let t' = C.Const (uri,exp_named_subst') in
              if l = [] then t' else C.Appl (t'::l)
         | C.Constant (_,None,_,_,_) ->
            let t' = C.Const (uri,exp_named_subst') in
             if l = [] then t' else C.Appl (t'::l)
         | C.Variable _ -> raise ReferenceToVariable
         | C.CurrentProof (_,_,body,_,_,_) -> reduceaux context l body
         | C.InductiveDefinition _ -> raise ReferenceToInductiveDefinition
       )
    | C.MutInd (uri,i,exp_named_subst) ->
       let exp_named_subst' =
        reduceaux_exp_named_subst context l exp_named_subst
       in
        let t' = C.MutInd (uri,i,exp_named_subst') in
         if l = [] then t' else C.Appl (t'::l)
    | C.MutConstruct (uri,i,j,exp_named_subst) ->
       let exp_named_subst' =
        reduceaux_exp_named_subst context l exp_named_subst
       in
        let t' = C.MutConstruct(uri,i,j,exp_named_subst') in
         if l = [] then t' else C.Appl (t'::l)
    | C.MutCase (mutind,i,outtype,term,pl) ->
       let decofix =
        function
           C.CoFix (i,fl) ->
             let (_,_,body) = List.nth fl i in
              let body' =
               let counter = ref (List.length fl) in
                List.fold_right
                 (fun _ -> decr counter ; S.subst (C.CoFix (!counter,fl)))
                 fl
                 body
              in
               reduceaux context [] body'
         | C.Appl (C.CoFix (i,fl) :: tl) ->
             let (_,_,body) = List.nth fl i in
             let body' =
              let counter = ref (List.length fl) in
               List.fold_right
                (fun _ -> decr counter ; S.subst (C.CoFix (!counter,fl)))
                fl
                body
             in
              let tl' = List.map (reduceaux context []) tl in
               reduceaux context tl' body'
         | t -> t
       in
        (match decofix (reduceaux context [] term) (*(CicReduction.whd context term)*) with
            C.MutConstruct (_,_,j,_) -> reduceaux context l (List.nth pl (j-1))
          | C.Appl (C.MutConstruct (_,_,j,_) :: tl) ->
             let (arity, r) =
	       let o,_ = CicEnvironment.get_obj CicUniv.oblivion_ugraph mutind in
		 match o with
                     C.InductiveDefinition (tl,ingredients,r,_) ->
                       let (_,_,arity,_) = List.nth tl i in
			 (arity,r)
		   | _ -> raise WrongUriToInductiveDefinition
             in
              let ts =
               let rec eat_first =
                function
                   (0,l) -> l
                 | (n,he::tl) when n > 0 -> eat_first (n - 1, tl)
                 | _ -> raise (Impossible 5)
               in
                eat_first (r,tl)
              in
               reduceaux context (ts@l) (List.nth pl (j-1))
         | C.Cast _ | C.Implicit _ ->
            raise (Impossible 2) (* we don't trust our whd ;-) *)
         | _ ->
           let outtype' = reduceaux context [] outtype in
           let term' = reduceaux context [] term in
           let pl' = List.map (reduceaux context []) pl in
            let res =
             C.MutCase (mutind,i,outtype',term',pl')
            in
             if l = [] then res else C.Appl (res::l)
       )
    | C.Fix (i,fl) ->
       let tys,_ =
         List.fold_left
           (fun (types,len) (n,_,ty,_) ->
              (Some (C.Name n,(C.Decl (CicSubstitution.lift len ty)))::types,
               len+1)
          ) ([],0) fl 
       in
        let t' () =
         let fl' =
          List.map
           (function (n,recindex,ty,bo) ->
             (n,recindex,reduceaux context [] ty, reduceaux (tys@context) [] bo)
           ) fl
         in
          C.Fix (i, fl')
        in
         let (_,recindex,_,body) = List.nth fl i in
          let recparam =
           try
            Some (List.nth l recindex)
           with
            _ -> None
          in
           (match recparam with
               Some recparam ->
                (match reduceaux context [] recparam with
                    C.MutConstruct _
                  | C.Appl ((C.MutConstruct _)::_) ->
                     let body' =
                      let counter = ref (List.length fl) in
                       List.fold_right
                        (fun _ -> decr counter ; S.subst (C.Fix (!counter,fl)))
                        fl
                        body
                     in
                      (* Possible optimization: substituting whd recparam in l*)
                      reduceaux context l body'
                  | _ -> if l = [] then t' () else C.Appl ((t' ())::l)
                )
             | None -> if l = [] then t' () else C.Appl ((t' ())::l)
           )
    | C.CoFix (i,fl) ->
       let tys,_ =
        List.fold_left
          (fun (types,len) (n,ty,_) ->
             (Some (C.Name n,(C.Decl (CicSubstitution.lift len ty)))::types,
              len+1)
         ) ([],0) fl
       in
        let t' =
         let fl' =
          List.map
           (function (n,ty,bo) ->
             (n,reduceaux context [] ty, reduceaux (tys@context) [] bo)
           ) fl
         in
         C.CoFix (i, fl')
       in
         if l = [] then t' else C.Appl (t'::l)
 and reduceaux_exp_named_subst context l =
  List.map (function uri,t -> uri,reduceaux context [] t)
 (**** Step 2 ****)
 and reduce_with_no_hope_to_fold_back t l =
    prerr_endline "reduce_with_no_hope_to_fold_back";
    let simplified = reduceaux context l t in
    let t' = if l = [] then t else C.Appl (t::l) in
    if t' = simplified then
      raise AlreadySimplified
    else
      simplified

 and try_delta_expansion context l term body =
   try
    let res,constant_args =
     let rec aux rev_constant_args l =
      function
         C.Lambda (name,s,t) ->
          begin
           match l with
              [] -> raise WrongShape
            | he::tl ->
               (* when name is Anonimous the substitution should *)
               (* be superfluous                                 *)
               aux (he::rev_constant_args) tl (S.subst he t)
          end
       | C.LetIn (_,s,_,t) ->
          aux rev_constant_args l (S.subst s t)
       | C.Fix (i,fl) ->
           let (_,recindex,_,body) = List.nth fl i in
            let recparam =
             try
              List.nth l recindex
             with
              _ -> raise AlreadySimplified
            in
             (match reduceaux context [] recparam (*CicReduction.whd context recparam*) with
                 C.MutConstruct _
               | C.Appl ((C.MutConstruct _)::_) ->
                  let body' =
                   let counter = ref (List.length fl) in
                    List.fold_right
                     (function _ ->
                       decr counter ; S.subst (C.Fix (!counter,fl))
                     ) fl body
                  in
                   (* Possible optimization: substituting whd *)
                   (* recparam in l                           *)
                   reduceaux context l body',
                    List.rev rev_constant_args
               | _ -> raise AlreadySimplified
             )
       | _ -> raise WrongShape
     in
      aux [] l body
    in
     (**** Step 3.1 ****)
     let term_to_fold, delta_expanded_term_to_fold =
      match constant_args with
         [] -> term,body
       | _ -> C.Appl (term::constant_args), C.Appl (body::constant_args)
     in
      let simplified_term_to_fold =
       reduceaux context [] delta_expanded_term_to_fold
      in
       replace_lifting ~equality:(fun _ x y -> x = y) ~context
         ~what:[simplified_term_to_fold] ~with_what:[term_to_fold] ~where:res
   with
      WrongShape ->
       let rec skip_lambda n = function
         | Cic.Lambda (_,_,t) -> skip_lambda (n+1) t | t -> t, n
       in
       let is_fix uri = 
         match fst(CicEnvironment.get_obj CicUniv.oblivion_ugraph uri) with
         | Cic.Constant (_,Some bo, _, _,_) ->
             (let t, _ = skip_lambda 0 bo in
             match t with | Cic.Fix _ -> true | _ -> false) 
         | _ -> false
       in
       let guess_recno uri = 
         prerr_endline ("GUESS: " ^ UriManager.string_of_uri uri);
         match fst(CicEnvironment.get_obj CicUniv.oblivion_ugraph uri) with
         | Cic.Constant (_,Some bo, _, _,_ ) -> 
             let t, n = skip_lambda 0 bo in
             (match t with
             | Cic.Fix (i,fl) ->
                 let _,recno,_,_ = List.nth fl i in
                 prerr_endline ("GUESSED: " ^ string_of_int recno ^ " after " ^
                 string_of_int n ^ " lambdas");
                 recno + n
             | _ -> assert false)    
         | _ -> assert false
       in
       let original_args = l in 
       (**** Step 3.2 ****)
       let rec aux l =
        function
         | C.Lambda (name,s,t) ->
             (match l with
              | [] -> raise AlreadySimplified
              | he::tl ->
                 (* when name is Anonimous the substitution should *)
                 (* be superfluous                                 *)
                 aux tl (S.subst he t))
         | C.LetIn (_,s,_,t) -> aux l (S.subst s t)
         | Cic.Appl (Cic.Const (uri,_) :: args) as t when is_fix uri ->
             let recno =
               prerr_endline ("cerco : " ^ string_of_int (guess_recno uri)
                 ^ " in: " ^ String.concat " " 
                 (List.map (fun x -> CicPp.ppterm x) args));
               prerr_endline ("e piglio il rispettivo in :"^String.concat " " 
                 (List.map (fun x -> CicPp.ppterm x) original_args));
               (* look for args[regno] in saved_args *)
               let wanted = List.nth (args@l) (guess_recno uri) in
               let rec aux n = function
                 | [] -> n (* DA CAPIRE *)
                 | t::_ when t = wanted -> n
                 | _::tl -> aux (n+1) tl
               in
               aux 0 original_args
             in
             if recno = List.length original_args then
               reduce_with_no_hope_to_fold_back t l
             else
               let simplified = reduceaux context l t in
               let rec mk_implicits = function
                 | n,_::tl when n = recno -> 
                     Cic.Implicit None :: (mk_implicits (n+1,tl))
                 | n,arg::tl -> arg :: (mk_implicits (n+1,tl))
                 | _,[] -> []
               in
               (* we try to fold back constant that do not expand to Fix *)
               let _ = prerr_endline 
                 ("INIZIO (" ^ string_of_int recno ^ ") : " ^ CicPp.ppterm
                 simplified) in
               let term_to_fold = 
                 Cic.Appl (term:: mk_implicits (0,original_args)) 
               in
               (try
                 let term_to_fold, _, metasenv, _ = 
                   CicRefine.type_of_aux' [] context term_to_fold
                     CicUniv.oblivion_ugraph
                 in
                 let _ = 
                   prerr_endline ("RAFFINA: "^CicPp.ppterm term_to_fold) in
                 let _ = 
                   prerr_endline 
                     ("RAFFINA: "^CicMetaSubst.ppmetasenv [] metasenv) in
                 let simplified_term_to_fold = unfold context term_to_fold in
                 let _ = 
                   prerr_endline ("SEMPLIFICA: " ^ 
                     CicPp.ppterm simplified_term_to_fold) 
                 in
                 let rec do_n f t = 
                   let t1 = f t in
                   if t1 = t then t else do_n f t1
                 in
                 do_n 
                 (fun simplified -> 
                   let subst = ref [] in
                   let myunif ctx t1 t2 =
                     if !subst <> [] then false 
                     else
                     try 
                       prerr_endline "MUNIF";
                       prerr_endline (CicPp.ppterm t1);
                       prerr_endline "VS";
                       prerr_endline (CicPp.ppterm t2 ^ "\n");
                       let subst1, _, _ = 
                         CicUnification.fo_unif metasenv ctx t1 t2
                           CicUniv.oblivion_ugraph
                       in
                       prerr_endline "UNIFICANO\n\n\n";
                       subst := subst1;
                       true
                     with 
                     | CicUnification.UnificationFailure s
                     | CicUnification.Uncertain s
                     | CicUnification.AssertFailure s ->
                         prerr_endline (Lazy.force s); false
                     | CicUtil.Meta_not_found _ -> false
                     (*
                     | _ as exn -> 
                         prerr_endline (Printexc.to_string exn);
                         false*)
                   in
                   let t = 
                     replace_lifting myunif context
                       [simplified_term_to_fold] [term_to_fold] simplified
                   in
                   let _ = prerr_endline "UNIFICA" in
                   if List.length metasenv <> List.length !subst then 
                     let _ = prerr_endline ("SUBST CORTA " ^
                       CicMetaSubst.ppsubst !subst ~metasenv) 
                     in
                       simplified 
                   else
                     if t = simplified then 
                       let _ = prerr_endline "NULLA DI FATTO" in
                       simplified 
                     else
                       let t = CicMetaSubst.apply_subst !subst t in
                       prerr_endline ("ECCO: " ^ CicPp.ppterm t); t)
                   simplified 
               with 
               | CicRefine.RefineFailure s 
               | CicRefine.Uncertain s
               | CicRefine.AssertFailure s ->
                   prerr_endline (Lazy.force s); simplified 
               (*| exn -> prerr_endline (Printexc.to_string exn); simplified*))
         | t -> reduce_with_no_hope_to_fold_back t l
      in
        (try aux l body
         with
          AlreadySimplified ->
           if l = [] then term else C.Appl (term::l))
    | AlreadySimplified ->
       (* If we performed delta-reduction, we would find a Fix   *)
       (* not applied to a constructor. So, we refuse to perform *)
       (* delta-reduction.                                       *)
       if l = [] then term else C.Appl (term::l)
 in
  reduceaux context []
;;
