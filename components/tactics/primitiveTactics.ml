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

exception TheTypeOfTheCurrentGoalIsAMetaICannotChooseTheRightElimiantionPrinciple
exception NotAnInductiveTypeToEliminate
exception WrongUriToVariable of string
exception NotAnEliminator

module PET = ProofEngineTypes

(* lambda_abstract newmeta ty *)
(* returns a triple [bo],[context],[ty'] where              *)
(* [ty] = Pi/LetIn [context].[ty'] ([context] is a vector!) *)
(* and [bo] = Lambda/LetIn [context].(Meta [newmeta])       *)
(* So, lambda_abstract is the core of the implementation of *)
(* the Intros tactic.                                       *)
(* howmany = -1 means Intros, howmany > 0 means Intros n    *)
let lambda_abstract ?(howmany=(-1)) metasenv context newmeta ty mk_fresh_name =
 let module C = Cic in
  let rec collect_context context howmany do_whd ty =
   match howmany with
   | 0 ->  
        let irl =
          CicMkImplicit.identity_relocation_list_for_metavariable context
        in
         context, ty, (C.Meta (newmeta,irl))
   | _ -> 
      match ty with 
        C.Cast (te,_)   -> collect_context context howmany do_whd te 
      | C.Prod (n,s,t)  ->
	 let n' = mk_fresh_name metasenv context n ~typ:s in
          let (context',ty,bo) =
           let entry = match n' with
	      | C.Name _    -> Some (n',(C.Decl s))
	      | C.Anonymous -> None
	   in
	   let ctx = entry :: context in
           collect_context ctx (howmany - 1) do_whd t 
          in
           (context',ty,C.Lambda(n',s,bo))
      | C.LetIn (n,s,sty,t) ->
         let (context',ty,bo) =
          collect_context ((Some (n,(C.Def (s,sty))))::context) (howmany - 1) do_whd t
         in
          (context',ty,C.LetIn(n,s,sty,bo))
      | _ as t ->
        if howmany <= 0 then
         let irl =
          CicMkImplicit.identity_relocation_list_for_metavariable context
         in
          context, t, (C.Meta (newmeta,irl))
        else if do_whd then
	  let t = CicReduction.whd ~delta:true context t in
	  collect_context context howmany false t
	else
         raise (PET.Fail (lazy "intro(s): not enough products or let-ins"))
  in
   collect_context context howmany true ty 

let eta_expand metasenv context t arg =
 let module T = CicTypeChecker in
 let module S = CicSubstitution in
 let module C = Cic in
  let rec aux n =
   function
      t' when t' = S.lift n arg -> C.Rel (1 + n)
    | C.Rel m  -> if m <= n then C.Rel m else C.Rel (m+1)
    | C.Var (uri,exp_named_subst) ->
       let exp_named_subst' = aux_exp_named_subst n exp_named_subst in
        C.Var (uri,exp_named_subst')
    | C.Meta (i,l) ->
       let l' =
        List.map (function None -> None | Some t -> Some (aux n t)) l
       in
        C.Meta (i, l')
    | C.Sort _
    | C.Implicit _ as t -> t
    | C.Cast (te,ty) -> C.Cast (aux n te, aux n ty)
    | C.Prod (nn,s,t) -> C.Prod (nn, aux n s, aux (n+1) t)
    | C.Lambda (nn,s,t) -> C.Lambda (nn, aux n s, aux (n+1) t)
    | C.LetIn (nn,s,ty,t) -> C.LetIn (nn, aux n s, aux n ty, aux (n+1) t)
    | C.Appl l -> C.Appl (List.map (aux n) l)
    | C.Const (uri,exp_named_subst) ->
       let exp_named_subst' = aux_exp_named_subst n exp_named_subst in
        C.Const (uri,exp_named_subst')
    | C.MutInd (uri,i,exp_named_subst) ->
       let exp_named_subst' = aux_exp_named_subst n exp_named_subst in
        C.MutInd (uri,i,exp_named_subst')
    | C.MutConstruct (uri,i,j,exp_named_subst) ->
       let exp_named_subst' = aux_exp_named_subst n exp_named_subst in
        C.MutConstruct (uri,i,j,exp_named_subst')
    | C.MutCase (sp,i,outt,t,pl) ->
       C.MutCase (sp,i,aux n outt, aux n t,
        List.map (aux n) pl)
    | C.Fix (i,fl) ->
       let tylen = List.length fl in
        let substitutedfl =
         List.map
          (fun (name,i,ty,bo) -> (name, i, aux n ty, aux (n+tylen) bo))
           fl
        in
         C.Fix (i, substitutedfl)
    | C.CoFix (i,fl) ->
       let tylen = List.length fl in
        let substitutedfl =
         List.map
          (fun (name,ty,bo) -> (name, aux n ty, aux (n+tylen) bo))
           fl
        in
         C.CoFix (i, substitutedfl)
  and aux_exp_named_subst n =
   List.map (function uri,t -> uri,aux n t)
  in
   let argty,_ = 
    T.type_of_aux' metasenv context arg CicUniv.oblivion_ugraph (* TASSI: FIXME *)
   in
    let fresh_name =
     FreshNamesGenerator.mk_fresh_name ~subst:[]
      metasenv context (Cic.Name "Heta") ~typ:argty
    in
     (C.Appl [C.Lambda (fresh_name,argty,aux 0 t) ; arg])

(*CSC: ma serve solamente la prima delle new_uninst e l'unione delle due!!! *)
let classify_metas newmeta in_subst_domain subst_in metasenv =
 List.fold_right
  (fun (i,canonical_context,ty) (old_uninst,new_uninst) ->
    if in_subst_domain i then
     old_uninst,new_uninst
    else
     let ty' = subst_in canonical_context ty in
      let canonical_context' =
       List.fold_right
        (fun entry canonical_context' ->
          let entry' =
           match entry with
              Some (n,Cic.Decl s) ->
               Some (n,Cic.Decl (subst_in canonical_context' s))
            | None -> None
            | Some (n,Cic.Def (bo,ty)) ->
               Some
                (n,
                  Cic.Def
                   (subst_in canonical_context' bo,
                    subst_in canonical_context' ty))
          in
           entry'::canonical_context'
        ) canonical_context []
     in
      if i < newmeta then
       ((i,canonical_context',ty')::old_uninst),new_uninst
      else
       old_uninst,((i,canonical_context',ty')::new_uninst)
  ) metasenv ([],[])

(* Useful only inside apply_tac *)
let
 generalize_exp_named_subst_with_fresh_metas context newmeta uri exp_named_subst
=
 let module C = Cic in
  let params =
    let o,_ = CicEnvironment.get_obj CicUniv.oblivion_ugraph uri in
    CicUtil.params_of_obj o
  in
   let exp_named_subst_diff,new_fresh_meta,newmetasenvfragment,exp_named_subst'=
    let next_fresh_meta = ref newmeta in
    let newmetasenvfragment = ref [] in
    let exp_named_subst_diff = ref [] in
     let rec aux =
      function
         [],[] -> []
       | uri::tl,[] ->
          let ty =
            let o,_ = CicEnvironment.get_obj CicUniv.oblivion_ugraph uri in
              match o with
                  C.Variable (_,_,ty,_,_) ->
                    CicSubstitution.subst_vars !exp_named_subst_diff ty
                | _ -> raise (WrongUriToVariable (UriManager.string_of_uri uri))
          in
(* CSC: patch to generate ?1 : ?2 : Type in place of ?1 : Type to simulate ?1 :< Type
           (match ty with
               C.Sort (C.Type _) as s -> (* TASSI: ?? *)
                 let fresh_meta = !next_fresh_meta in
                 let fresh_meta' = fresh_meta + 1 in
                  next_fresh_meta := !next_fresh_meta + 2 ;
                  let subst_item = uri,C.Meta (fresh_meta',[]) in
                   newmetasenvfragment :=
                    (fresh_meta,[],C.Sort (C.Type (CicUniv.fresh()))) ::
                     (* TASSI: ?? *)
                     (fresh_meta',[],C.Meta (fresh_meta,[])) :: !newmetasenvfragment ;
                   exp_named_subst_diff := !exp_named_subst_diff @ [subst_item] ;
                   subst_item::(aux (tl,[]))
             | _ ->
*)
              let irl =
                CicMkImplicit.identity_relocation_list_for_metavariable context
              in
              let subst_item = uri,C.Meta (!next_fresh_meta,irl) in
               newmetasenvfragment :=
                (!next_fresh_meta,context,ty)::!newmetasenvfragment ;
               exp_named_subst_diff := !exp_named_subst_diff @ [subst_item] ;
               incr next_fresh_meta ;
               subst_item::(aux (tl,[]))(*)*)
       | uri::tl1,((uri',_) as s)::tl2 ->
          assert (UriManager.eq uri uri') ;
          s::(aux (tl1,tl2))
       | [],_ -> assert false
     in
      let exp_named_subst' = aux (params,exp_named_subst) in
       !exp_named_subst_diff,!next_fresh_meta,
        List.rev !newmetasenvfragment, exp_named_subst'
   in
    new_fresh_meta,newmetasenvfragment,exp_named_subst',exp_named_subst_diff
;;

let new_metasenv_and_unify_and_t newmeta' metasenv' subst context term' ty termty goal_arity =
  let (consthead,newmetasenv,arguments,_) =
   TermUtil.saturate_term newmeta' metasenv' context termty
    goal_arity in
  let subst,newmetasenv',_ = 
   CicUnification.fo_unif_subst 
     subst context newmetasenv consthead ty CicUniv.oblivion_ugraph
  in
  let t = 
    if List.length arguments = 0 then term' else Cic.Appl (term'::arguments)
  in
  subst,newmetasenv',t

let rec count_prods subst context ty =
 match CicReduction.whd ~subst context ty with
    Cic.Prod (n,s,t) -> 1 + count_prods subst (Some (n,Cic.Decl s)::context) t
  | _ -> 0

let apply_with_subst ~term ~maxmeta (proof, goal) =
  (* Assumption: The term "term" must be closed in the current context *)
 let module T = CicTypeChecker in
 let module R = CicReduction in
 let module C = Cic in
  let (_,metasenv,subst,_,_, _) = proof in
  let metano,context,ty = CicUtil.lookup_meta goal metasenv in
  let newmeta = max (CicMkImplicit.new_meta metasenv subst) maxmeta in
   let exp_named_subst_diff,newmeta',newmetasenvfragment,term' =
    match term with
       C.Var (uri,exp_named_subst) ->
        let newmeta',newmetasenvfragment,exp_named_subst',exp_named_subst_diff =
         generalize_exp_named_subst_with_fresh_metas context newmeta uri
          exp_named_subst
        in
         exp_named_subst_diff,newmeta',newmetasenvfragment,
          C.Var (uri,exp_named_subst')
     | C.Const (uri,exp_named_subst) ->
        let newmeta',newmetasenvfragment,exp_named_subst',exp_named_subst_diff =
         generalize_exp_named_subst_with_fresh_metas context newmeta uri
          exp_named_subst
        in
         exp_named_subst_diff,newmeta',newmetasenvfragment,
          C.Const (uri,exp_named_subst')
     | C.MutInd (uri,tyno,exp_named_subst) ->
        let newmeta',newmetasenvfragment,exp_named_subst',exp_named_subst_diff =
         generalize_exp_named_subst_with_fresh_metas context newmeta uri
          exp_named_subst
        in
         exp_named_subst_diff,newmeta',newmetasenvfragment,
          C.MutInd (uri,tyno,exp_named_subst')
     | C.MutConstruct (uri,tyno,consno,exp_named_subst) ->
        let newmeta',newmetasenvfragment,exp_named_subst',exp_named_subst_diff =
         generalize_exp_named_subst_with_fresh_metas context newmeta uri
          exp_named_subst
        in
         exp_named_subst_diff,newmeta',newmetasenvfragment,
          C.MutConstruct (uri,tyno,consno,exp_named_subst')
     | _ -> [],newmeta,[],term
   in
   let metasenv' = metasenv@newmetasenvfragment in
   let termty,_ = 
     CicTypeChecker.type_of_aux' 
       metasenv' ~subst context term' CicUniv.oblivion_ugraph
   in
   let termty =
     CicSubstitution.subst_vars exp_named_subst_diff termty in
   let goal_arity = count_prods subst context ty in
   let subst,newmetasenv',t = 
    let rec add_one_argument n =
     try
      new_metasenv_and_unify_and_t newmeta' metasenv' subst context term' ty
        termty n
     with CicUnification.UnificationFailure _ when n > 0 ->
      add_one_argument (n - 1)
    in
     add_one_argument goal_arity
   in
   let in_subst_domain i = List.exists (function (j,_) -> i=j) subst in
   let apply_subst = CicMetaSubst.apply_subst subst in
   let old_uninstantiatedmetas,new_uninstantiatedmetas =
     (* subst_in doesn't need the context. Hence the underscore. *)
     let subst_in _ = CicMetaSubst.apply_subst subst in
     classify_metas newmeta in_subst_domain subst_in newmetasenv'
   in
   let bo' = apply_subst t in
   let newmetasenv'' = new_uninstantiatedmetas@old_uninstantiatedmetas in
   let subst_in =
     (* if we just apply the subtitution, the type is irrelevant:
              we may use Implicit, since it will be dropped *)
      ((metano,(context,bo',Cic.Implicit None))::subst)
   in
   let (newproof, newmetasenv''') = 
    ProofEngineHelpers.subst_meta_and_metasenv_in_proof proof metano subst_in
     newmetasenv''
   in
   let subst = ((metano,(context,bo',ty))::subst) in
   let newproof = 
     let u,m,_,p,t,l = newproof in
     u,m,subst,p,t,l
   in
   subst,
   (newproof, List.map (function (i,_,_) -> i) new_uninstantiatedmetas),
   max maxmeta (CicMkImplicit.new_meta newmetasenv''' subst)


(* ALB *)
let apply_with_subst ~term ?(subst=[]) ?(maxmeta=0) status =
  try
    let status = 
      if subst <> [] then
        let (u,m,_,p,t,l), g = status in (u,m,subst,p,t,l), g
      else status
    in
     apply_with_subst ~term ~maxmeta status
  with 
  | CicUnification.UnificationFailure msg
  | CicTypeChecker.TypeCheckerFailure msg -> raise (PET.Fail msg)

(* ALB *)
let apply_tac_verbose ~term status =
  let subst, status, _ = apply_with_subst ~term status in
  (CicMetaSubst.apply_subst subst), status

let apply_tac ~term status = snd (apply_tac_verbose ~term status)

  (* TODO per implementare i tatticali e' necessario che tutte le tattiche
  sollevino _solamente_ Fail *)
let apply_tac ~term =
 let apply_tac ~term status =
  try
    apply_tac ~term status
      (* TODO cacciare anche altre eccezioni? *)
  with 
  | CicUnification.UnificationFailure msg
  | CicTypeChecker.TypeCheckerFailure msg ->
      raise (PET.Fail msg)
 in
  PET.mk_tactic (apply_tac ~term)

let applyP_tac ~term =
   let applyP_tac status =
      let res = PET.apply_tactic (apply_tac ~term) status in res
   in
   PET.mk_tactic applyP_tac

let intros_tac ?howmany ?(mk_fresh_name_callback = FreshNamesGenerator.mk_fresh_name ~subst:[]) ()=
 let intros_tac (proof, goal)
 =
  let module C = Cic in
  let module R = CicReduction in
   let (_,metasenv,_subst,_,_, _) = proof in
   let metano,context,ty = CicUtil.lookup_meta goal metasenv in
    let newmeta = ProofEngineHelpers.new_meta_of_proof ~proof in
     let (context',ty',bo') =
      lambda_abstract ?howmany metasenv context newmeta ty mk_fresh_name_callback
     in
      let (newproof, _) =
       ProofEngineHelpers.subst_meta_in_proof proof metano bo'
        [newmeta,context',ty']
      in
       (newproof, [newmeta])
 in
  PET.mk_tactic intros_tac
  
let cut_tac ?(mk_fresh_name_callback = FreshNamesGenerator.mk_fresh_name ~subst:[]) term =
 let cut_tac
  ?(mk_fresh_name_callback = FreshNamesGenerator.mk_fresh_name ~subst:[])
  term (proof, goal)
 =
  let module C = Cic in
   let curi,metasenv,_subst,pbo,pty, attrs = proof in
   let metano,context,ty = CicUtil.lookup_meta goal metasenv in
    let newmeta1 = ProofEngineHelpers.new_meta_of_proof ~proof in
    let newmeta2 = newmeta1 + 1 in
    let fresh_name =
     mk_fresh_name_callback metasenv context (Cic.Name "Hcut") ~typ:term in
    let context_for_newmeta1 =
     (Some (fresh_name,C.Decl term))::context in
    let irl1 =
     CicMkImplicit.identity_relocation_list_for_metavariable
      context_for_newmeta1
    in
    let irl2 =
      CicMkImplicit.identity_relocation_list_for_metavariable context
    in
     let newmeta1ty = CicSubstitution.lift 1 ty in
      let bo' = 
        Cic.LetIn (fresh_name, C.Meta (newmeta2,irl2), term, C.Meta (newmeta1,irl1))
      in
      let (newproof, _) =
       ProofEngineHelpers.subst_meta_in_proof proof metano bo'
        [newmeta2,context,term; newmeta1,context_for_newmeta1,newmeta1ty];
      in
       (newproof, [newmeta1 ; newmeta2])
 in
  PET.mk_tactic (cut_tac ~mk_fresh_name_callback term)

let letin_tac ?(mk_fresh_name_callback=FreshNamesGenerator.mk_fresh_name ~subst:[]) term =
 let letin_tac
  ?(mk_fresh_name_callback = FreshNamesGenerator.mk_fresh_name ~subst:[])
  term (proof, goal)
 =
  let module C = Cic in
   let curi,metasenv,_subst,pbo,pty, attrs = proof in
   (* occur check *)
   let occur i t =
     let m = CicUtil.metas_of_term t in 
     List.exists (fun (j,_) -> i=j) m
   in
   let metano,context,ty = CicUtil.lookup_meta goal metasenv in
   if occur metano term then
     raise 
       (ProofEngineTypes.Fail (lazy
         "You can't letin a term containing the current goal"));
    let tty,_ =
      CicTypeChecker.type_of_aux' metasenv context term CicUniv.oblivion_ugraph in
     let newmeta = ProofEngineHelpers.new_meta_of_proof ~proof in
     let fresh_name =
      mk_fresh_name_callback metasenv context (Cic.Name "Hletin") ~typ:term in
     let context_for_newmeta =
      (Some (fresh_name,C.Def (term,tty)))::context in
     let irl =
      CicMkImplicit.identity_relocation_list_for_metavariable
       context_for_newmeta
     in
      let newmetaty = CicSubstitution.lift 1 ty in
      let bo' = C.LetIn (fresh_name,term,tty,C.Meta (newmeta,irl)) in
       let (newproof, _) =
         ProofEngineHelpers.subst_meta_in_proof
           proof metano bo'[newmeta,context_for_newmeta,newmetaty]
       in
        (newproof, [newmeta])
 in
  PET.mk_tactic (letin_tac ~mk_fresh_name_callback term)

(* FG: exact_tac := apply_tac as in NTactics *)
let exact_tac ~term = apply_tac ~term

(* not really "primitive" tactics .... *)
  
module TC  = CicTypeChecker
module UM  = UriManager
module R   = CicReduction
module C   = Cic
module PEH = ProofEngineHelpers
module PER = ProofEngineReduction
module MS  = CicMetaSubst 
module S   = CicSubstitution 
module T   = Tacticals
module RT  = ReductionTactics

let rec args_init n f =
   if n <= 0 then [] else f n :: args_init (pred n) f

let mk_predicate_for_elim 
 ~context ~metasenv ~subst ~ugraph ~goal ~arg ~using ~cpattern ~args_no 
= 
   let instantiated_eliminator =
      let f n = if n = 1 then arg else C.Implicit None in
      C.Appl (using :: args_init args_no f)
   in
   let _actual_arg, iety, _metasenv', _ugraph = 
      CicRefine.type_of_aux' metasenv context instantiated_eliminator ugraph
   in
   let _actual_meta, actual_args = match iety with
      | C.Meta (i, _)                  -> i, []
      | C.Appl (C.Meta (i, _) :: args) -> i, args
      | _                              -> assert false
   in
(* let _, upto = PEH.split_with_whd (List.nth splits pred_pos) in *)
   let rec mk_pred metasenv subst context' pred arg' cpattern' = function
      | []           -> metasenv, subst, pred, arg'
      | arg :: tail -> 
(* FG: we find the predicate for the eliminator as in the rewrite tactic ****)
	 let argty, _ = TC.type_of_aux' metasenv ~subst context arg ugraph in
         let argty = CicReduction.whd ~subst context argty in         
         let fresh_name = 
            FreshNamesGenerator.mk_fresh_name 
            ~subst metasenv context' C.Anonymous ~typ:argty in
	 let hyp = Some (fresh_name, C.Decl argty) in
         let lazy_term c m u =  
          let distance  = List.length c - List.length context in
           S.lift distance arg, m, u in
         let pattern = Some lazy_term, [], Some cpattern' in
         let subst, metasenv, _ugraph, _conjecture, selected_terms =
          ProofEngineHelpers.select ~subst ~metasenv ~ugraph
           ~conjecture:(0, context, pred) ~pattern in
         let metasenv = MS.apply_subst_metasenv subst metasenv in  
         let map (_context_of_t, t) l = t :: l in
         let what = List.fold_right map selected_terms [] in
         let arg' = MS.apply_subst subst arg' in
         let pred = PER.replace_with_rel_1_from ~equality:(==) ~what 1 pred in
         let pred = MS.apply_subst subst pred in
	 let pred = C.Lambda (fresh_name, C.Implicit None, pred) in
	 let cpattern' = C.Lambda (C.Anonymous, C.Implicit None, cpattern') in
         mk_pred metasenv subst (hyp :: context') pred arg' cpattern' tail 
   in
   let metasenv, subst, pred, arg = 
      mk_pred metasenv subst context goal arg cpattern (List.rev actual_args)
   in
   HLog.debug ("PREDICATE CONTEXT:\n" ^ CicPp.ppcontext ~metasenv context);
   HLog.debug ("PREDICATE: " ^ CicPp.ppterm ~metasenv pred ^ " ARGS: " ^ String.concat " " (List.map (CicPp.ppterm ~metasenv) actual_args));
   metasenv, subst, pred, arg, actual_args

let beta_after_elim_tac upto predicate =
   let beta_after_elim_tac status =
      let proof, goal = status in
      let _, metasenv, _subst, _, _, _ = proof in
      let _, _, ty = CicUtil.lookup_meta goal metasenv in
      let mk_pattern ~equality ~upto ~predicate ty =
         (* code adapted from ProceduralConversion.generalize *)
	 let meta = C.Implicit None in
         let hole = C.Implicit (Some `Hole) in
	 let anon = C.Anonymous in
         let is_meta =
            let map b = function
               | C.Implicit None when b -> b
	       | _                      -> false
            in
            List.fold_left map true
         in
         let rec gen_fix len k (name, i, ty, bo) =
            name, i, gen_term k ty, gen_term (k + len) bo
         and gen_cofix len k (name, ty, bo) =
            name, gen_term k ty, gen_term (k + len) bo
         and gen_term k = function
            | C.Sort _ 
            | C.Implicit _
            | C.Const (_, _)
            | C.Var (_, _)
            | C.MutInd (_, _, _)
            | C.MutConstruct (_, _, _, _)
            | C.Meta (_, _) 
            | C.Rel _ -> meta
            | C.Appl (hd :: tl) when equality hd (S.lift k predicate) ->
	       assert (List.length tl = upto);
	       hole
	    | C.Appl ts -> 
               let ts = List.map (gen_term k) ts in
               if is_meta ts then meta else C.Appl ts
            | C.Cast (te, ty) -> 
               let te, ty = gen_term k te, gen_term k ty in
	       if is_meta [te; ty] then meta else C.Cast (te, ty)
            | C.MutCase (sp, i, outty, t, pl) ->         
	       let outty, t, pl = gen_term k outty, gen_term k t, List.map (gen_term k) pl in
	       if is_meta (outty :: t :: pl) then meta else hole (* C.MutCase (sp, i, outty, t, pl) *)
            | C.Prod (_, s, t) -> 
               let s, t = gen_term k s, gen_term (succ k) t in
               if is_meta [s; t] then meta else C.Prod (anon, s, t)
            | C.Lambda (_, s, t) ->
               let s, t = gen_term k s, gen_term (succ k) t in
               if is_meta [s; t] then meta else C.Lambda (anon, s, t)
            | C.LetIn (_, s, ty, t) -> 
               let s,ty,t = gen_term k s, gen_term k ty, gen_term (succ k) t in
               if is_meta [s; t] then meta else C.LetIn (anon, s, ty, t)
            | C.Fix (i, fl) -> C.Fix (i, List.map (gen_fix (List.length fl) k) fl)
            | C.CoFix (i, fl) -> C.CoFix (i, List.map (gen_cofix (List.length fl) k) fl)
         in
         None, [], Some (gen_term 0 ty)
      in
      let equality = CicUtil.alpha_equivalence in
      let pattern = mk_pattern ~equality ~upto ~predicate ty in
      let tactic = RT.head_beta_reduce_tac ~delta:false ~upto ~pattern in
      PET.apply_tactic tactic status
   in
   PET.mk_tactic beta_after_elim_tac

(* ANCORA DA DEBUGGARE *)

exception UnableToDetectTheTermThatMustBeGeneralizedYouMustGiveItExplicitly;;
exception TheSelectedTermsMustLiveInTheGoalContext
exception AllSelectedTermsMustBeConvertible;;
exception GeneralizationInHypothesesNotImplementedYet;;

let generalize_tac 
 ?(mk_fresh_name_callback = FreshNamesGenerator.mk_fresh_name ~subst:[])
 pattern
 =
  let module PET = ProofEngineTypes in
  let generalize_tac mk_fresh_name_callback
       ~pattern:(term,hyps_pat,_) status
  =
   if hyps_pat <> [] then raise GeneralizationInHypothesesNotImplementedYet;
   let (proof, goal) = status in
   let module C = Cic in
   let module T = Tacticals in
    let uri,metasenv,subst,pbo,pty, attrs = proof in
    let (_,context,ty) as conjecture = CicUtil.lookup_meta goal metasenv in
    let subst,metasenv,u,selected_hyps,terms_with_context =
     ProofEngineHelpers.select ~metasenv ~subst ~ugraph:CicUniv.oblivion_ugraph
      ~conjecture ~pattern in
    let context = CicMetaSubst.apply_subst_context subst context in
    let metasenv = CicMetaSubst.apply_subst_metasenv subst metasenv in
    let pbo = lazy (CicMetaSubst.apply_subst subst (Lazy.force pbo)) in
    let pty = CicMetaSubst.apply_subst subst pty in
    let term =
     match term with
        None -> None
      | Some term ->
          Some (fun context metasenv ugraph -> 
                  let term, metasenv, ugraph = term context metasenv ugraph in
                   CicMetaSubst.apply_subst subst term,
                    CicMetaSubst.apply_subst_metasenv subst metasenv,
                    ugraph)
    in
    let u,typ,term, metasenv' =
     let context_of_t, (t, metasenv, u) =
      match terms_with_context, term with
         [], None ->
          raise
           UnableToDetectTheTermThatMustBeGeneralizedYouMustGiveItExplicitly
       | [], Some t -> context, t context metasenv u
       | (context_of_t, _)::_, Some t -> 
           context_of_t, t context_of_t metasenv u
       | (context_of_t, t)::_, None -> context_of_t, (t, metasenv, u)
     in
      let t,e_subst,metasenv' =
       try
        CicMetaSubst.delift_rels [] metasenv
         (List.length context_of_t - List.length context) t
       with
        CicMetaSubst.DeliftingARelWouldCaptureAFreeVariable ->
         raise TheSelectedTermsMustLiveInTheGoalContext
      in
       (*CSC: I am not sure about the following two assertions;
         maybe I need to propagate the new subst and metasenv *)
       assert (e_subst = []);
       assert (metasenv' = metasenv);
       let typ,u = CicTypeChecker.type_of_aux' ~subst metasenv context t u in
        u,typ,t,metasenv
    in
    (* We need to check:
        1. whether they live in the context of the goal;
           if they do they are also well-typed since they are closed subterms
           of a well-typed term in the well-typed context of the well-typed
           term
        2. whether they are convertible
    *)
    ignore (
     List.fold_left
      (fun u (context_of_t,t) ->
        (* 1 *)
        let t,subst,metasenv'' =
         try
          CicMetaSubst.delift_rels [] metasenv'
           (List.length context_of_t - List.length context) t
         with
          CicMetaSubst.DeliftingARelWouldCaptureAFreeVariable ->
           raise TheSelectedTermsMustLiveInTheGoalContext in
        (*CSC: I am not sure about the following two assertions;
          maybe I need to propagate the new subst and metasenv *)
        assert (subst = []);
        assert (metasenv'' = metasenv');
        (* 2 *)
        let b,u1 = CicReduction.are_convertible ~subst context term t u in 
         if not b then 
          raise AllSelectedTermsMustBeConvertible
         else
          u1
      ) u terms_with_context) ;
    let status = (uri,metasenv',subst,pbo,pty, attrs),goal in
    let proof,goals =
     PET.apply_tactic 
      (T.thens 
        ~start:
          (cut_tac 
           (C.Prod(
             (mk_fresh_name_callback metasenv context C.Anonymous ~typ:typ), 
             typ,
             (ProofEngineReduction.replace_lifting_csc 1
               ~equality:(==) 
               ~what:(List.map snd terms_with_context)
               ~with_what:(List.map (function _ -> C.Rel 1) terms_with_context)
               ~where:ty)
           )))
        ~continuations:
          [(apply_tac ~term:(C.Appl [C.Rel 1; CicSubstitution.lift 1 term])) ;
            T.id_tac])
        status
    in
     let _,metasenv'',_,_,_, _ = proof in
      (* CSC: the following is just a bad approximation since a meta
         can be closed and then re-opened! *)
      (proof,
        goals @
         (List.filter
           (fun j -> List.exists (fun (i,_,_) -> i = j) metasenv'')
           (ProofEngineHelpers.compare_metasenvs ~oldmetasenv:metasenv
             ~newmetasenv:metasenv')))
 in
  PET.mk_tactic (generalize_tac mk_fresh_name_callback ~pattern)
;;

let generalize_pattern_tac pattern =
 let generalize_pattern_tac (proof,goal) =
   let _,metasenv,_,_,_,_ = proof in
   let conjecture = CicUtil.lookup_meta goal metasenv in
   let _,context,_ = conjecture in 
   let generalize_hyps =
    let _,hpatterns,_ = ProofEngineHelpers.sort_pattern_hyps context pattern in
     List.map fst hpatterns in
   let ids_and_patterns =
    List.map
     (fun id ->
       let rel,_ = ProofEngineHelpers.find_hyp id context in
        id,(Some (fun ctx m u -> CicSubstitution.lift (List.length ctx - List.length context) rel,m,u), [], Some (ProofEngineTypes.hole))
     ) generalize_hyps in
   let tactics =
    List.map
     (function (id,pattern) ->
       Tacticals.then_ ~start:(generalize_tac pattern)
        ~continuation:(Tacticals.try_tactic
          (ProofEngineStructuralRules.clear [id]))
     ) ids_and_patterns
   in
    PET.apply_tactic (Tacticals.seq tactics) (proof,goal)
 in
  PET.mk_tactic (generalize_pattern_tac)
;;

let pattern_after_generalize_pattern_tac (tp, hpatterns, cpattern) =
 let cpattern =
  match cpattern with
     None -> ProofEngineTypes.hole
   | Some t -> t
 in
 let cpattern =
  List.fold_left
   (fun t (_,ty) -> Cic.Prod (Cic.Anonymous, ty, t)) cpattern hpatterns
 in
  tp, [], Some cpattern
;;

let elim_tac ?using ?(pattern = PET.conclusion_pattern None) term = 
 let elim_tac pattern (proof, goal) =
   let ugraph = CicUniv.oblivion_ugraph in
   let curi, metasenv, subst, proofbo, proofty, attrs = proof in
   let conjecture = CicUtil.lookup_meta goal metasenv in
   let metano, context, ty = conjecture in 
   let pattern = pattern_after_generalize_pattern_tac pattern in
   let cpattern =
    match pattern with 
      | None, [], Some cpattern -> cpattern
      | _ -> raise (PET.Fail (lazy "not implemented")) in    
    let termty,_ugraph = TC.type_of_aux' metasenv ~subst context term ugraph in
    let termty = CicReduction.whd ~subst context termty in
    let termty, metasenv', arguments, _fresh_meta =
     TermUtil.saturate_term
      (ProofEngineHelpers.new_meta_of_proof proof) metasenv context termty 0 in
    let term = if arguments = [] then term else Cic.Appl (term::arguments) in
    let uri, exp_named_subst, typeno, _args =
     match termty with
        C.MutInd (uri,typeno,exp_named_subst) -> (uri,exp_named_subst,typeno,[])
      | C.Appl ((C.MutInd (uri,typeno,exp_named_subst))::args) ->
          (uri,exp_named_subst,typeno,args)
      | _ -> raise NotAnInductiveTypeToEliminate
    in
     let eliminator_uri =
      let buri = UM.buri_of_uri uri in
      let name = 
        let o,_ugraph = CicEnvironment.get_obj ugraph uri in
       match o with
          C.InductiveDefinition (tys,_,_,_) ->
           let (name,_,_,_) = List.nth tys typeno in
            name
        | _ -> assert false
      in
      let ty_ty,_ugraph = TC.type_of_aux' metasenv' ~subst context ty ugraph in
      let ext =
       match ty_ty with
          C.Sort C.Prop -> "_ind"
        | C.Sort C.Set  -> "_rec"
        | C.Sort (C.CProp _) -> "_rect"
        | C.Sort (C.Type _)-> "_rect" 
        | C.Meta (_,_) -> raise TheTypeOfTheCurrentGoalIsAMetaICannotChooseTheRightElimiantionPrinciple
        | _ -> assert false
      in
       UM.uri_of_string (buri ^ "/" ^ name ^ ext ^ ".con")
     in
      let eliminator_ref = match using with
         | None   -> C.Const (eliminator_uri, exp_named_subst)
         | Some t -> t 
       in
       let ety, _ugraph = 
         TC.type_of_aux' metasenv' ~subst context eliminator_ref ugraph in
(* FG: ADDED PART ***********************************************************)
(* FG: we can not assume eliminator is the default eliminator ***************)
   let splits, args_no = PEH.split_with_whd (context, ety) in
   let pred_pos = match List.hd splits with
      | _, C.Rel i when i > 1 && i <= args_no -> i
      | _, C.Appl (C.Rel i :: _) when i > 1 && i <= args_no -> i
      | _ -> raise NotAnEliminator
   in
   let metasenv', subst, pred, term, actual_args = match pattern with 
      | None, [], Some (C.Implicit (Some `Hole)) ->
         metasenv', subst, C.Implicit None, term, []
      | _                                        ->
         mk_predicate_for_elim 
	    ~args_no ~context ~ugraph ~cpattern
	    ~metasenv:metasenv' ~subst ~arg:term ~using:eliminator_ref ~goal:ty
   in
(* FG: END OF ADDED PART ****************************************************)
      let term_to_refine =
         let f n =
            if n = pred_pos then pred else
            if n = 1 then term else C.Implicit None
         in
         C.Appl (eliminator_ref :: args_init args_no f)
      in
      let refined_term,_refined_termty,metasenv'',subst,_ugraph = 
         CicRefine.type_of metasenv' subst context term_to_refine ugraph
      in
      let ipred = match refined_term with
         | C.Appl ts -> List.nth ts (List.length ts - pred_pos)
	 | _         -> assert false
      in
      let new_goals =
         ProofEngineHelpers.compare_metasenvs
            ~oldmetasenv:metasenv ~newmetasenv:metasenv''
      in
      let proof' = curi,metasenv'',subst,proofbo,proofty, attrs in
      let proof'', new_goals' =
         PET.apply_tactic (apply_tac ~term:refined_term) (proof',goal)
      in
      (* The apply_tactic can have closed some of the new_goals *)
      let patched_new_goals =
         let (_,metasenv''',_,_,_, _) = proof'' in
         List.filter
            (function i -> List.exists (function (j,_,_) -> j=i) metasenv''')
	    new_goals @ new_goals'
      in
      let res = proof'', patched_new_goals in
      let upto = List.length actual_args in
      if upto = 0 then res else
(* FG: we use ipred (instantiated pred) instead of pred (not instantiated) *)
      let continuation = beta_after_elim_tac upto ipred in
      let dummy_status = proof,goal in
      PET.apply_tactic
         (T.then_ ~start:(PET.mk_tactic (fun _ -> res)) ~continuation)
         dummy_status
   in
   let reorder_pattern ((proof, goal) as status) =
     let _,metasenv,_,_,_,_ = proof in
     let conjecture = CicUtil.lookup_meta goal metasenv in
     let _,context,_ = conjecture in
     let pattern = ProofEngineHelpers.sort_pattern_hyps context pattern in
      PET.apply_tactic
       (Tacticals.then_ ~start:(generalize_pattern_tac pattern)
         ~continuation:(PET.mk_tactic (elim_tac pattern))) status
   in
    PET.mk_tactic reorder_pattern
;;

let cases_intros_tac ?(howmany=(-1)) ?(mk_fresh_name_callback = FreshNamesGenerator.mk_fresh_name ~subst:[]) ?(pattern = PET.conclusion_pattern None) term =
 let cases_tac pattern (proof, goal) =
  let module TC = CicTypeChecker in
  let module U = UriManager in
  let module R = CicReduction in
  let module C = Cic in
  let (curi,metasenv,_subst, proofbo,proofty, attrs) = proof in
  let metano,context,ty = CicUtil.lookup_meta goal metasenv in
  let pattern = pattern_after_generalize_pattern_tac pattern in
  let _cpattern =
   match pattern with 
     | None, [], Some cpattern ->
        let rec is_hole =
         function
            Cic.Implicit (Some `Hole) -> true
          | Cic.Prod (Cic.Anonymous,so,tgt) -> is_hole so && is_hole tgt
          | _ -> false
        in
         if not (is_hole cpattern) then
          raise (PET.Fail (lazy "not implemented"))
     | _ -> raise (PET.Fail (lazy "not implemented")) in    
  let termty,_ = TC.type_of_aux' metasenv context term CicUniv.oblivion_ugraph in
  let termty = CicReduction.whd context termty in
  let (termty,metasenv',arguments,fresh_meta) =
   TermUtil.saturate_term
    (ProofEngineHelpers.new_meta_of_proof proof) metasenv context termty 0 in
  let term = if arguments = [] then term else Cic.Appl (term::arguments) in
  let uri,exp_named_subst,typeno,args =
    match termty with
    | C.MutInd (uri,typeno,exp_named_subst) -> (uri,exp_named_subst,typeno,[])
    | C.Appl ((C.MutInd (uri,typeno,exp_named_subst))::args) ->
        (uri,exp_named_subst,typeno,args)
    | _ -> raise NotAnInductiveTypeToEliminate
  in
  let paramsno,itty,patterns,right_args =
    match CicEnvironment.get_obj CicUniv.oblivion_ugraph uri with
    | C.InductiveDefinition (tys,_,paramsno,_),_ ->
       let _,left_parameters,right_args = 
         List.fold_right 
           (fun x (n,acc1,acc2) -> 
             if n > 0 then (n-1,acc1,x::acc2) else (n,x::acc1,acc2)) 
           args (List.length args - paramsno, [],[])
       in
       let _,_,itty,cl = List.nth tys typeno in
       let rec aux left_parameters context t =
         match left_parameters,CicReduction.whd context t with
         | [],C.Prod (name,source,target) ->
            let fresh_name =
              mk_fresh_name_callback metasenv' context name ~typ:source
            in
             C.Lambda (fresh_name,C.Implicit None,
             aux [] (Some (fresh_name,C.Decl source)::context) target)
         | hd::tl,C.Prod (name,source,target) ->
             (* left parameters instantiation *)
             aux tl context (CicSubstitution.subst hd target)
         | [],_ -> C.Implicit None
         | _ -> assert false
       in
        paramsno,itty,
        List.map (function (_,cty) -> aux left_parameters context cty) cl,
        right_args
    | _ -> assert false
  in
  let outtypes =
    let n_right_args = List.length right_args in
    let n_lambdas = n_right_args + 1 in
    let lifted_ty = CicSubstitution.lift n_lambdas ty in
    let captured_ty = 
      let what = 
        List.map (CicSubstitution.lift n_lambdas) (right_args)
      in
      let with_what meta = 
        let rec mkargs = function 
          | 0 -> assert false
          | 1 -> []
          | n -> 
              (if meta then Cic.Implicit None else Cic.Rel n)::(mkargs (n-1)) 
        in
        mkargs n_lambdas 
      in
      let replaced = ref false in
      let replace = ProofEngineReduction.replace_lifting
       ~equality:(fun _ a b -> let rc = CicUtil.alpha_equivalence a b in 
                  if rc then replaced := true; rc)
       ~context:[]
      in
      let captured = 
        replace ~what:[CicSubstitution.lift n_lambdas term] 
          ~with_what:[Cic.Rel 1] ~where:lifted_ty
      in
      if not !replaced then
        (* this means the matched term is not there, 
         * but maybe right params are: we user rels (to right args lambdas) *)
        [replace ~what ~with_what:(with_what false) ~where:captured]
      else
        (* since the matched is there, rights should be inferrable *)
        [replace ~what ~with_what:(with_what false) ~where:captured;
         replace ~what ~with_what:(with_what true) ~where:captured]
    in
    let captured_term_ty = 
      let term_ty = CicSubstitution.lift n_right_args termty in
      let rec mkrels = function 0 -> []|n -> (Cic.Rel n)::(mkrels (n-1)) in
      let rec fstn acc l n = 
        if n = 0 then acc else fstn (acc@[List.hd l]) (List.tl l) (n-1) 
      in
      match term_ty with
      | C.MutInd _ -> term_ty
      | C.Appl ((C.MutInd (a,b,c))::args) -> 
           C.Appl ((C.MutInd (a,b,c))::
               fstn [] args paramsno @ mkrels n_right_args)
      | _ -> raise NotAnInductiveTypeToEliminate
    in
    let rec add_lambdas captured_ty = function
      | 0 -> captured_ty
      | 1 -> 
          C.Lambda (C.Name "matched", captured_term_ty, (add_lambdas captured_ty 0))
      | n -> 
           C.Lambda (C.Name ("right_"^(string_of_int (n-1))),
                     C.Implicit None, (add_lambdas captured_ty (n-1)))
    in
    List.map (fun x -> add_lambdas x n_lambdas) captured_ty
  in
  let rec first = (* easier than using tacticals *)
  function 
  | [] -> raise (PET.Fail (lazy ("unable to generate a working outtype")))
  | outtype::rest -> 
     let term_to_refine = C.MutCase (uri,typeno,outtype,term,patterns) in
     try
       let refined_term,_,metasenv'',_ = 
         CicRefine.type_of_aux' metasenv' context term_to_refine
           CicUniv.oblivion_ugraph
       in
       let new_goals =
         ProofEngineHelpers.compare_metasenvs
           ~oldmetasenv:metasenv ~newmetasenv:metasenv''
       in
       let proof' = curi,metasenv'',_subst,proofbo,proofty, attrs in
         let proof'', new_goals' =
           PET.apply_tactic (apply_tac ~term:refined_term) (proof',goal)
         in
         (* The apply_tactic can have closed some of the new_goals *)
         let patched_new_goals =
           let (_,metasenv''',_subst,_,_,_) = proof'' in
             List.filter
               (function i -> List.exists (function (j,_,_) -> j=i) metasenv''')
               new_goals @ new_goals'
         in
         proof'', patched_new_goals
     with PET.Fail _ | CicRefine.RefineFailure _ | CicRefine.Uncertain _ -> first rest
  in
   first outtypes
 in
   let reorder_pattern ((proof, goal) as status) =
     let _,metasenv,_,_,_,_ = proof in
     let conjecture = CicUtil.lookup_meta goal metasenv in
     let _,context,_ = conjecture in
     let pattern = ProofEngineHelpers.sort_pattern_hyps context pattern in
      PET.apply_tactic
       (Tacticals.then_ ~start:(generalize_pattern_tac pattern)
         ~continuation:(PET.mk_tactic (cases_tac pattern))) status
   in
    PET.mk_tactic reorder_pattern
;;


let elim_intros_tac ?(mk_fresh_name_callback = FreshNamesGenerator.mk_fresh_name ~subst:[]) 
                    ?depth ?using ?pattern what =
 Tacticals.then_ ~start:(elim_tac ?using ?pattern what)
  ~continuation:(intros_tac ~mk_fresh_name_callback ?howmany:depth ())
;;

(* The simplification is performed only on the conclusion *)
let elim_intros_simpl_tac ?(mk_fresh_name_callback = FreshNamesGenerator.mk_fresh_name ~subst:[])
                          ?depth ?using ?pattern what =
 Tacticals.then_ ~start:(elim_tac ?using ?pattern what)
  ~continuation:
   (Tacticals.thens
     ~start:(intros_tac ~mk_fresh_name_callback ?howmany:depth ())
     ~continuations:
       [ReductionTactics.simpl_tac
         ~pattern:(ProofEngineTypes.conclusion_pattern None)])
;;
