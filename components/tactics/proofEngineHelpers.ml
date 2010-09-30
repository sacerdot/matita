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

exception Bad_pattern of string Lazy.t

let new_meta_of_proof ~proof:(_, metasenv, subst, _, _, _) =
  CicMkImplicit.new_meta metasenv subst

let subst_meta_in_proof proof meta term newmetasenv =
 let uri,metasenv,initial_subst,bo,ty, attrs = proof in
   (* empty context is ok for term since it wont be used by apply_subst *)
   (* hack: since we do not know the context and the type of term, we
      create a substitution with cc =[] and type = Implicit; they will be
      in  any case dropped by apply_subst, but it would be better to rewrite
      the code. Cannot we just use apply_subst_metasenv, etc. ?? *)
  let subst_in = CicMetaSubst.apply_subst [meta,([], term,Cic.Implicit None)] in
   let metasenv' =
    newmetasenv @ (List.filter (function (m,_,_) -> m <> meta) metasenv)
   in
    let metasenv'' =
     List.map
      (function i,canonical_context,ty ->
        let canonical_context' =
         List.map
          (function
              Some (n,Cic.Decl s) -> Some (n,Cic.Decl (subst_in s))
            | None -> None
            | Some (n,Cic.Def (bo,ty)) ->
               Some (n,Cic.Def (subst_in bo,subst_in ty))
          ) canonical_context
        in
         i,canonical_context',(subst_in ty)
      ) metasenv'
    in
     let bo' = lazy (subst_in (Lazy.force bo)) in
     (* Metavariables can appear also in the *statement* of the theorem
      * since the parser does not reject as statements terms with
      * metavariable therein *)
     let ty' = subst_in ty in
      let newproof = uri,metasenv'',initial_subst,bo',ty', attrs in
       (newproof, metasenv'')

(*CSC: commento vecchio *)
(* refine_meta_with_brand_new_metasenv meta term subst_in newmetasenv     *)
(* This (heavy) function must be called when a tactic can instantiate old *)
(* metavariables (i.e. existential variables). It substitues the metasenv *)
(* of the proof with the result of removing [meta] from the domain of     *)
(* [newmetasenv]. Then it replaces Cic.Meta [meta] with [term] everywhere *)
(* in the current proof. Finally it applies [apply_subst_replacing] to    *)
(*  current proof.                                                        *)
(*CSC: A questo punto perche' passare un bo' gia' istantiato, se tanto poi *)
(*CSC: ci ripasso sopra apply_subst!!!                                     *)
(*CSC: Attenzione! Ora questa funzione applica anche [subst_in] a *)
(*CSC: [newmetasenv].                                             *)
let subst_meta_and_metasenv_in_proof proof meta subst newmetasenv =
 let (uri,_,initial_subst,bo,ty, attrs) = proof in
  let subst_in = CicMetaSubst.apply_subst subst in
  let bo' = lazy (subst_in (Lazy.force bo)) in
  (* Metavariables can appear also in the *statement* of the theorem
   * since the parser does not reject as statements terms with
   * metavariable therein *)
  let ty' = subst_in ty in
  let metasenv' =
   List.fold_right
    (fun metasenv_entry i ->
      match metasenv_entry with
         (m,canonical_context,ty) when m <> meta ->
           let canonical_context' =
            List.map
             (function
                 None -> None
               | Some (i,Cic.Decl t) -> Some (i,Cic.Decl (subst_in t))
               | Some (i,Cic.Def (bo,ty)) ->
                  Some (i,Cic.Def (subst_in bo,subst_in ty))
             ) canonical_context
           in
            (m,canonical_context',subst_in ty)::i
       | _ -> i
    ) newmetasenv []
  in
  (* qui da capire se per la fase transitoria si fa initial_subst @ subst
   * oppure subst *)
   let newproof = uri,metasenv',subst,bo',ty', attrs in
    (newproof, metasenv')

let compare_metasenvs ~oldmetasenv ~newmetasenv =
 List.map (function (i,_,_) -> i)
  (List.filter
   (function (i,_,_) ->
     not (List.exists (fun (j,_,_) -> i=j) oldmetasenv)) newmetasenv)
;;

(** finds the _pointers_ to subterms that are alpha-equivalent to wanted in t *)
let find_subterms ~subst ~metasenv ~ugraph ~wanted ~context t =
  let rec find subst metasenv ugraph context w t =
   try
    let subst,metasenv,ugraph =
     CicUnification.fo_unif_subst subst context metasenv w t ugraph
    in
      subst,metasenv,ugraph,[context,t]
   with
     CicUnification.UnificationFailure _
   | CicUnification.Uncertain _ ->
      match t with
      | Cic.Sort _ 
      | Cic.Rel _ -> subst,metasenv,ugraph,[]
      | Cic.Meta (_, ctx) -> 
          List.fold_left (
            fun (subst,metasenv,ugraph,acc) e -> 
              match e with 
              | None -> subst,metasenv,ugraph,acc 
              | Some t ->
                 let subst,metasenv,ugraph,res =
                  find subst metasenv ugraph context w t
                 in
                  subst,metasenv,ugraph, res @ acc
          ) (subst,metasenv,ugraph,[]) ctx
      | Cic.Lambda (name, t1, t2) 
      | Cic.Prod (name, t1, t2) ->
         let subst,metasenv,ugraph,rest1 =
          find subst metasenv ugraph context w t1 in
         let subst,metasenv,ugraph,rest2 =
          find subst metasenv ugraph (Some (name, Cic.Decl t1)::context)
           (CicSubstitution.lift 1 w) t2
         in
          subst,metasenv,ugraph,rest1 @ rest2
      | Cic.LetIn (name, t1, t2, t3) -> 
         let subst,metasenv,ugraph,rest1 =
          find subst metasenv ugraph context w t1 in
         let subst,metasenv,ugraph,rest2 =
          find subst metasenv ugraph context w t2 in
         let subst,metasenv,ugraph,rest3 =
          find subst metasenv ugraph (Some (name, Cic.Def (t1,t2))::context)
           (CicSubstitution.lift 1 w) t3
         in
          subst,metasenv,ugraph,rest1 @ rest2 @ rest3
      | Cic.Appl l -> 
          List.fold_left
           (fun (subst,metasenv,ugraph,acc) t ->
             let subst,metasenv,ugraph,res =
              find subst metasenv ugraph context w t
             in
              subst,metasenv,ugraph,res @ acc)
           (subst,metasenv,ugraph,[]) l
      | Cic.Cast (t, ty) ->
         let subst,metasenv,ugraph,rest =
          find subst metasenv ugraph context w t in
         let subst,metasenv,ugraph,resty =
          find subst metasenv ugraph context w ty
         in
          subst,metasenv,ugraph,rest @ resty
      | Cic.Implicit _ -> assert false
      | Cic.Const (_, esubst)
      | Cic.Var (_, esubst) 
      | Cic.MutInd (_, _, esubst) 
      | Cic.MutConstruct (_, _, _, esubst) -> 
          List.fold_left
           (fun (subst,metasenv,ugraph,acc) (_, t) ->
             let subst,metasenv,ugraph,res =
              find subst metasenv ugraph context w t
             in
              subst,metasenv,ugraph,res @ acc)
           (subst,metasenv,ugraph,[]) esubst
      | Cic.MutCase (_, _, outty, indterm, patterns) -> 
         let subst,metasenv,ugraph,resoutty =
          find subst metasenv ugraph context w outty in
         let subst,metasenv,ugraph,resindterm =
          find subst metasenv ugraph context w indterm in
         let subst,metasenv,ugraph,respatterns =
          List.fold_left
           (fun (subst,metasenv,ugraph,acc) p ->
             let subst,metaseng,ugraph,res =
              find subst metasenv ugraph context w p
             in
              subst,metasenv,ugraph,res @ acc
           ) (subst,metasenv,ugraph,[]) patterns
         in
          subst,metasenv,ugraph,resoutty @ resindterm @ respatterns
      | Cic.Fix (_, funl) -> 
         let tys =
          List.map (fun (n,_,ty,_) -> Some (Cic.Name n,(Cic.Decl ty))) funl
         in
          List.fold_left (
            fun (subst,metasenv,ugraph,acc) (_, _, ty, bo) ->
             let subst,metasenv,ugraph,resty =
              find subst metasenv ugraph context w ty in
             let subst,metasenv,ugraph,resbo =
              find subst metasenv ugraph (tys @ context) w bo
             in
              subst,metasenv,ugraph, resty @ resbo @ acc
          ) (subst,metasenv,ugraph,[]) funl
      | Cic.CoFix (_, funl) ->
         let tys =
          List.map (fun (n,ty,_) -> Some (Cic.Name n,(Cic.Decl ty))) funl
         in
          List.fold_left (
            fun (subst,metasenv,ugraph,acc) (_, ty, bo) ->
             let subst,metasenv,ugraph,resty =
              find subst metasenv ugraph context w ty in
             let subst,metasenv,ugraph,resbo =
              find subst metasenv ugraph (tys @ context) w bo
             in
              subst,metasenv,ugraph, resty @ resbo @ acc
          ) (subst,metasenv,ugraph,[]) funl
  in
  find subst metasenv ugraph context wanted t
  
let select_in_term 
  ~metasenv ~subst ~context ~ugraph ~term ~pattern:(wanted,where) 
=
  let add_ctx context name entry = (Some (name, entry)) :: context in
  let map2 error_msg f l1 l2 = 
    try 
      List.map2 f l1 l2 
    with
    | Invalid_argument _ -> raise (Bad_pattern (lazy error_msg))
  in
  let rec aux context where term =
    match (where, term) with
    | Cic.Implicit (Some `Hole), t -> [context,t]
    | Cic.Implicit (Some `Type), t -> []
    | Cic.Implicit None,_ -> []
    | Cic.Meta (_, ctxt1), Cic.Meta (_, ctxt2) ->
        List.concat
          (map2 "wrong number of argument in explicit substitution"
            (fun t1 t2 ->
              (match (t1, t2) with
                  Some t1, Some t2 -> aux context t1 t2
                | _ -> []))
            ctxt1 ctxt2)
    | Cic.Cast (te1, ty1), Cic.Cast (te2, ty2) ->
       aux context te1 te2 @ aux context ty1 ty2
    | Cic.Prod (Cic.Anonymous, s1, t1), Cic.Prod (name, s2, t2)
    | Cic.Lambda (Cic.Anonymous, s1, t1), Cic.Lambda (name, s2, t2) ->
        aux context s1 s2 @ aux (add_ctx context name (Cic.Decl s2)) t1 t2
    | Cic.Prod (Cic.Name n1, s1, t1), 
      Cic.Prod ((Cic.Name n2) as name , s2, t2)
    | Cic.Lambda (Cic.Name n1, s1, t1), 
      Cic.Lambda ((Cic.Name n2) as name, s2, t2) when n1 = n2->
        aux context s1 s2 @ aux (add_ctx context name (Cic.Decl s2)) t1 t2
    | Cic.Prod (name1, s1, t1), Cic.Prod (name2, s2, t2)
    | Cic.Lambda (name1, s1, t1), Cic.Lambda (name2, s2, t2) -> []
    | Cic.LetIn (Cic.Anonymous, s1, ty1, t1), Cic.LetIn (name, s2, ty2, t2) -> 
        aux context s1 s2 @
        aux context ty1 ty2 @
        aux (add_ctx context name (Cic.Def (s2,ty2))) t1 t2
    | Cic.LetIn (Cic.Name n1, s1, ty1, t1), 
      Cic.LetIn ((Cic.Name n2) as name, s2, ty2, t2) when n1 = n2-> 
        aux context s1 s2 @
        aux context ty1 ty2 @
        aux (add_ctx context name (Cic.Def (s2,ty2))) t1 t2
    | Cic.LetIn (name1, s1, ty1, t1), Cic.LetIn (name2, s2, ty2, t2) -> []
    | Cic.Appl terms1, Cic.Appl terms2 -> auxs context terms1 terms2
    | Cic.Var (_, subst1), Cic.Var (_, subst2)
    | Cic.Const (_, subst1), Cic.Const (_, subst2)
    | Cic.MutInd (_, _, subst1), Cic.MutInd (_, _, subst2)
    | Cic.MutConstruct (_, _, _, subst1), Cic.MutConstruct (_, _, _, subst2) ->
        auxs context (List.map snd subst1) (List.map snd subst2)
    | Cic.MutCase (_, _, out1, t1, pat1), Cic.MutCase (_ , _, out2, t2, pat2) ->
        aux context out1 out2 @ aux context t1 t2 @ auxs context pat1 pat2
    | Cic.Fix (_, funs1), Cic.Fix (_, funs2) ->
       let tys =
        List.map (fun (n,_,ty,_) -> Some (Cic.Name n,(Cic.Decl ty))) funs2
       in
        List.concat
          (map2 "wrong number of mutually recursive functions"
            (fun (_, _, ty1, bo1) (_, _, ty2, bo2) -> 
              aux context ty1 ty2 @ aux (tys @ context) bo1 bo2)
            funs1 funs2)
    | Cic.CoFix (_, funs1), Cic.CoFix (_, funs2) ->
       let tys =
        List.map (fun (n,ty,_) -> Some (Cic.Name n,(Cic.Decl ty))) funs2
       in
        List.concat
          (map2 "wrong number of mutually co-recursive functions"
            (fun (_, ty1, bo1) (_, ty2, bo2) ->
              aux context ty1 ty2 @ aux (tys @ context) bo1 bo2)
            funs1 funs2)
    | x,y -> 
        raise (Bad_pattern 
                (lazy (Printf.sprintf "Pattern %s versus term %s" 
                  (CicPp.ppterm x)
                  (CicPp.ppterm y))))
  and auxs context terms1 terms2 =  (* as aux for list of terms *)
    List.concat (map2 "wrong number of arguments in application"
      (fun t1 t2 -> aux context t1 t2) terms1 terms2)
  in
   let roots =
     match where with
     | None -> []
     | Some where -> aux context where term
   in
    match wanted with
       None -> subst,metasenv,ugraph,roots
     | Some wanted ->
        let rec find_in_roots subst =
         function
            [] -> subst,metasenv,ugraph,[]
          | (context',where)::tl ->
             let subst,metasenv,ugraph,tl' = find_in_roots subst tl in
             let subst,metasenv,ugraph,found =
              let wanted, metasenv, ugraph = wanted context' metasenv ugraph in
               find_subterms ~subst ~metasenv ~ugraph ~wanted ~context:context'
                where
             in
              subst,metasenv,ugraph,found @ tl'
        in
         find_in_roots subst roots
;;

(** create a pattern from a term and a list of subterms.
* the pattern is granted to have a ? for every subterm that has no selected
* subterms
* @param equality equality function used while walking the term. Defaults to
* physical equality (==) *)
let pattern_of ?(equality=(==)) ~term terms =
  let (===) x y = equality x y in
  let not_found = false, Cic.Implicit None in
  let rec aux t =
    match t with
    | t when List.exists (fun t' -> t === t') terms ->
       true,Cic.Implicit (Some `Hole)
    | Cic.Var (uri, subst) ->
       let b,subst = aux_subst subst in
        if b then
         true,Cic.Var (uri, subst)
        else
         not_found
    | Cic.Meta (i, ctxt) ->
        let b,ctxt =
          List.fold_right
           (fun e (b,ctxt) ->
             match e with
                None -> b,None::ctxt
              | Some t -> let bt,t = aux t in b||bt ,Some t::ctxt
           ) ctxt (false,[])
        in
         if b then
          true,Cic.Meta (i, ctxt)
         else
          not_found
    | Cic.Cast (te, ty) ->
       let b1,te = aux te in
       let b2,ty = aux ty in
        if b1||b2 then true,Cic.Cast (te, ty)
        else
         not_found
    | Cic.Prod (_, s, t) ->
       let b1,s = aux s in
       let b2,t = aux t in
        if b1||b2 then
         true, Cic.Prod (Cic.Anonymous, s, t)
        else
         not_found
    | Cic.Lambda (_, s, t) ->
       let b1,s = aux s in
       let b2,t = aux t in
        if b1||b2 then
         true, Cic.Lambda (Cic.Anonymous, s, t)
        else
         not_found
    | Cic.LetIn (_, s, ty, t) ->
       let b1,s = aux s in
       let b2,ty = aux ty in
       let b3,t = aux t in
        if b1||b2||b3 then
         true, Cic.LetIn (Cic.Anonymous, s, ty, t)
        else
         not_found
    | Cic.Appl terms ->
       let b,terms =
        List.fold_right
         (fun t (b,terms) ->
           let bt,t = aux t in
            b||bt,t::terms
         ) terms (false,[])
       in
        if b then
         true,Cic.Appl terms
        else
         not_found
    | Cic.Const (uri, subst) ->
       let b,subst = aux_subst subst in
        if b then
         true, Cic.Const (uri, subst)
        else
         not_found
    | Cic.MutInd (uri, tyno, subst) ->
       let b,subst = aux_subst subst in
        if b then
         true, Cic.MutInd (uri, tyno, subst)
        else
         not_found
    | Cic.MutConstruct (uri, tyno, consno, subst) ->
       let b,subst = aux_subst subst in
        if b then
         true, Cic.MutConstruct (uri, tyno, consno, subst)
        else
         not_found
    | Cic.MutCase (uri, tyno, outty, t, pat) ->
       let b1,outty = aux outty in
       let b2,t = aux t in
       let b3,pat =
        List.fold_right
         (fun t (b,pat) ->
           let bt,t = aux t in
            bt||b,t::pat
         ) pat (false,[])
       in
        if b1 || b2 || b3 then
         true, Cic.MutCase (uri, tyno, outty, t, pat)
        else
         not_found
    | Cic.Fix (funno, funs) ->
        let b,funs =
          List.fold_right
           (fun (name, i, ty, bo) (b,funs) ->
             let b1,ty = aux ty in
             let b2,bo = aux bo in
              b||b1||b2, (name, i, ty, bo)::funs) funs (false,[])
        in
         if b then
          true, Cic.Fix (funno, funs)
         else
          not_found
    | Cic.CoFix (funno, funs) ->
        let b,funs =
          List.fold_right
           (fun (name, ty, bo) (b,funs) ->
             let b1,ty = aux ty in
             let b2,bo = aux bo in
              b||b1||b2, (name, ty, bo)::funs) funs (false,[])
        in
         if b then
          true, Cic.CoFix (funno, funs)
         else
          not_found
    | Cic.Rel _
    | Cic.Sort _
    | Cic.Implicit _ -> not_found
  and aux_subst subst =
    List.fold_right
     (fun (uri, t) (b,subst) ->
       let b1,t = aux t in
        b||b1,(uri, t)::subst) subst (false,[])
  in
   snd (aux term)

exception Fail of string Lazy.t

  (** select metasenv conjecture pattern
  * select all subterms of [conjecture] matching [pattern].
  * It returns the set of matched terms (that can be compared using physical
  * equality to the subterms of [conjecture]) together with their contexts.
  * The representation of the set mimics the ProofEngineTypes.pattern type:
  * a list of hypothesis (names of) together with the list of its matched
  * subterms (and their contexts) + the list of matched subterms of the
  * with their context conclusion. Note: in the result the list of hypothesis
  * has an entry for each entry in the context and in the same order.
  * Of course the list of terms (with their context) associated to the
  * hypothesis name may be empty. 
  *
  * @raise Bad_pattern
  * *)
  let select ~metasenv ~subst ~ugraph ~conjecture:(_,context,ty)
       ~(pattern: (Cic.term, Cic.lazy_term) ProofEngineTypes.pattern)
  =
   let what, hyp_patterns, goal_pattern = pattern in
   let find_pattern_for name =
     try Some (snd (List.find (fun (n, pat) -> Cic.Name n = name) hyp_patterns))
     with Not_found -> None in
   (* Multiple hypotheses with the same name can be in the context.
      In this case we need to pick the last one, but we will perform
      a fold_right on the context. Thus we pre-process hyp_patterns. *)
   let full_hyp_pattern =
    let rec aux blacklist =
     function
        [] -> []
      | None::tl -> None::aux blacklist tl
      | Some (name,_)::tl ->
         if List.mem name blacklist then
          None::aux blacklist tl
         else
          find_pattern_for name::aux (name::blacklist) tl
    in
     aux [] context
   in
   let subst,metasenv,ugraph,ty_terms =
    select_in_term ~metasenv ~subst ~context ~ugraph ~term:ty
     ~pattern:(what,goal_pattern) 
   in
   let subst,metasenv,ugraph,context_terms =
    let subst,metasenv,ugraph,res,_ =
     (List.fold_right
      (fun (pattern,entry) (subst,metasenv,ugraph,res,context) ->
        match entry with
          None -> subst,metasenv,ugraph,None::res,None::context
        | Some (name,Cic.Decl term) ->
            (match pattern with
            | None ->
               subst,metasenv,ugraph,((Some (`Decl []))::res),(entry::context)
            | Some pat ->
                let subst,metasenv,ugraph,terms =
                 select_in_term ~subst ~metasenv ~context ~ugraph ~term
                  ~pattern:(what, Some pat)
                in
                 subst,metasenv,ugraph,((Some (`Decl terms))::res),
                  (entry::context))
        | Some (name,Cic.Def (bo, ty)) ->
            (match pattern with
            | None ->
               let selected_ty = [] in
                subst,metasenv,ugraph,((Some (`Def ([],selected_ty)))::res),
                 (entry::context)
            | Some pat -> 
                let subst,metasenv,ugraph,terms_bo =
                 select_in_term ~subst ~metasenv ~context ~ugraph ~term:bo
                  ~pattern:(what, Some pat) in
                let subst,metasenv,ugraph,terms_ty =
                 let subst,metasenv,ugraph,res =
                  select_in_term ~subst ~metasenv ~context ~ugraph ~term:ty
                   ~pattern:(what, Some pat)
                 in
                  subst,metasenv,ugraph,res
                in
                 subst,metasenv,ugraph,((Some (`Def (terms_bo,terms_ty)))::res),
                  (entry::context))
      ) (List.combine full_hyp_pattern context) (subst,metasenv,ugraph,[],[]))
    in
     subst,metasenv,ugraph,res
   in
    subst,metasenv,ugraph,context_terms, ty_terms
;;

(** locate_in_term equality what where context
* [what] must match a subterm of [where] according to [equality]
* It returns the matched terms together with their contexts in [where]
* [equality] defaults to physical equality
* [context] must be the context of [where]
*)
let locate_in_term ?(equality=(fun _ -> (==))) what ~where context =
  let add_ctx context name entry =
      (Some (name, entry)) :: context in
  let rec aux context where =
   if equality context what where then [context,where]
   else
    match where with
    | Cic.Implicit _
    | Cic.Meta _
    | Cic.Rel _
    | Cic.Sort _
    | Cic.Var _
    | Cic.Const _
    | Cic.MutInd _
    | Cic.MutConstruct _ -> []
    | Cic.Cast (te, ty) -> aux context te @ aux context ty
    | Cic.Prod (name, s, t)
    | Cic.Lambda (name, s, t) ->
        aux context s @ aux (add_ctx context name (Cic.Decl s)) t
    | Cic.LetIn (name, s, ty, t) -> 
        aux context s @
        aux context ty @
        aux (add_ctx context name (Cic.Def (s,ty))) t
    | Cic.Appl tl -> auxs context tl
    | Cic.MutCase (_, _, out, t, pat) ->
        aux context out @ aux context t @ auxs context pat
    | Cic.Fix (_, funs) ->
       let tys =
        List.map (fun (n,_,ty,_) -> Some (Cic.Name n,(Cic.Decl ty))) funs
       in
        List.concat
          (List.map
            (fun (_, _, ty, bo) -> 
              aux context ty @ aux (tys @ context) bo)
            funs)
    | Cic.CoFix (_, funs) ->
       let tys =
        List.map (fun (n,ty,_) -> Some (Cic.Name n,(Cic.Decl ty))) funs
       in
        List.concat
          (List.map
            (fun (_, ty, bo) ->
              aux context ty @ aux (tys @ context) bo)
            funs)
  and auxs context tl =  (* as aux for list of terms *)
    List.concat (List.map (fun t -> aux context t) tl)
  in
   aux context where

(** locate_in_conjecture equality what where context
* [what] must match a subterm of [where] according to [equality]
* It returns the matched terms together with their contexts in [where]
* [equality] defaults to physical equality
* [context] must be the context of [where]
*)
let locate_in_conjecture ?(equality=fun _ -> (==)) what (_,context,ty) =
 let context,res =
  List.fold_right
   (fun entry (context,res) ->
     match entry with
        None -> entry::context, res
      | Some (_, Cic.Decl ty) ->
         let res = res @ locate_in_term what ~where:ty context in
         let context' = entry::context in
          context',res
      | Some (_, Cic.Def (bo,ty)) ->
         let res = res @ locate_in_term what ~where:bo context in
         let res = res @ locate_in_term what ~where:ty context in
         let context' = entry::context in
          context',res
   ) context ([],[])
 in
  res @ locate_in_term what ~where:ty context

let lookup_type metasenv context hyp =
   let rec aux p = function
      | Some (Cic.Name name, Cic.Decl t) :: _ when name = hyp -> p, t
      | Some (Cic.Name name, Cic.Def (_,t)) :: _ when name = hyp -> p, t
      | _ :: tail -> aux (succ p) tail
      | [] -> raise (ProofEngineTypes.Fail (lazy "lookup_type: not premise in the current goal"))
   in
   aux 1 context

let find_hyp name =
 let rec find_hyp n =
  function
     [] -> assert false
   | Some (Cic.Name s,Cic.Decl ty)::_ when name = s ->
      Cic.Rel n, CicSubstitution.lift n ty
   | Some (Cic.Name s,Cic.Def _)::_ when name = s -> assert false (*CSC: not implemented yet! But does this make any sense?*)
   | _::tl -> find_hyp (n+1) tl
 in
  find_hyp 1
;;

(* sort pattern hypotheses from the smallest to the highest Rel *)
let sort_pattern_hyps context (t,hpatterns,cpattern) =
 let hpatterns =
  List.sort
   (fun (id1,_) (id2,_) ->
     let t1,_ = find_hyp id1 context in
     let t2,_ = find_hyp id2 context in
     match t1,t2 with
        Cic.Rel n1, Cic.Rel n2 -> compare n1 n2
      | _,_ -> assert false) hpatterns
 in
  t,hpatterns,cpattern
;;

(* FG: **********************************************************************)

let get_name context index =
   try match List.nth context (pred index) with
      | Some (Cic.Name name, _)     -> Some name
      | _                           -> None
   with Invalid_argument "List.nth" -> None

let get_rel context name =
   let rec aux i = function
      | []                                      -> None
      | Some (Cic.Name s, _) :: _ when s = name -> Some (Cic.Rel i)
      | _ :: tl                                 -> aux (succ i) tl
   in
   aux 1 context

let split_with_whd (c, t) =
   let add s v c = Some (s, Cic.Decl v) :: c in
   let rec aux whd a n c = function
      | Cic.Prod (s, v, t)  -> aux false ((c, v) :: a) (succ n) (add s v c) t
      | v when whd          -> (c, v) :: a, n
      | v                   -> aux true a n c (CicReduction.whd c v)
    in
    aux false [] 0 c t

let split_with_normalize (c, t) =
   let add s v c = Some (s, Cic.Decl v) :: c in
   let rec aux a n c = function
      | Cic.Prod (s, v, t)  -> aux ((c, v) :: a) (succ n) (add s v c) t
      | v                   -> (c, v) :: a, n
    in
    aux [] 0 c (CicReduction.normalize c t)

  (* menv sorting *)
module OT = 
  struct 
    type t = Cic.conjecture
    let compare (i,_,_) (j,_,_) = Pervasives.compare i j
  end
module MS = HTopoSort.Make(OT)
let relations_of_menv m c =
  let i, ctx, ty = c in
  let m = List.filter (fun (j,_,_) -> j <> i) m in
  let m_ty = List.map fst (CicUtil.metas_of_term ty) in
  let m_ctx = 
    List.flatten
      (List.map 
        (function 
         | None -> []
         | Some (_,Cic.Decl t) ->
             List.map fst (CicUtil.metas_of_term ty)
         | Some (_,Cic.Def (t,ty)) -> 
             List.map fst (CicUtil.metas_of_term ty) @
             List.map fst (CicUtil.metas_of_term t))
        ctx)
  in
  let metas = HExtlib.list_uniq (List.sort compare (m_ty @ m_ctx)) in
  List.filter (fun (i,_,_) -> List.exists ((=) i) metas) m
;;
let sort_metasenv (m : Cic.metasenv) =
  (MS.topological_sort m (relations_of_menv m) : Cic.metasenv)
;;
