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

(* $Id$ *)

open Printf

exception RefineFailure of string Lazy.t;;
exception Uncertain of string Lazy.t;;
exception AssertFailure of string Lazy.t;;

(* for internal use only; the integer is the number of surplus arguments *)
exception MoreArgsThanExpected of int * exn;;

let insert_coercions = ref true
let pack_coercions = ref true

let debug = false;;

let debug_print = 
  if debug then (fun x -> prerr_endline (Lazy.force x)) else (fun _ -> ());;

let profiler_eat_prods2 = HExtlib.profile "CicRefine.fo_unif_eat_prods2"

let fo_unif_subst_eat_prods2 subst context metasenv t1 t2 ugraph =
  try
let foo () =
    CicUnification.fo_unif_subst subst context metasenv t1 t2 ugraph
in profiler_eat_prods2.HExtlib.profile foo ()
  with
      (CicUnification.UnificationFailure msg) -> raise (RefineFailure msg)
    | (CicUnification.Uncertain msg) -> raise (Uncertain msg)
;;

let profiler_eat_prods = HExtlib.profile "CicRefine.fo_unif_eat_prods"

let fo_unif_subst_eat_prods subst context metasenv t1 t2 ugraph =
  try
let foo () =
    CicUnification.fo_unif_subst subst context metasenv t1 t2 ugraph
in profiler_eat_prods.HExtlib.profile foo ()
  with
      (CicUnification.UnificationFailure msg) -> raise (RefineFailure msg)
    | (CicUnification.Uncertain msg) -> raise (Uncertain msg)
;;

let profiler = HExtlib.profile "CicRefine.fo_unif"

let fo_unif_subst subst context metasenv t1 t2 ugraph =
  try
let foo () =
    CicUnification.fo_unif_subst subst context metasenv t1 t2 ugraph
in profiler.HExtlib.profile foo ()
  with
      (CicUnification.UnificationFailure msg) -> raise (RefineFailure msg)
    | (CicUnification.Uncertain msg) -> raise (Uncertain msg)
;;

let enrich localization_tbl t ?(f = fun msg -> msg) exn =
 let exn' =
  match exn with
     RefineFailure msg -> RefineFailure (f msg)
   | Uncertain msg -> Uncertain (f msg)
   | AssertFailure msg -> prerr_endline (Lazy.force msg); AssertFailure (f msg)
   | Sys.Break -> raise exn
   | _ -> prerr_endline (Printexc.to_string exn); assert false 
 in
 let loc =
  try
   Cic.CicHash.find localization_tbl t
  with Not_found ->
   HLog.debug ("!!! NOT LOCALIZED: " ^ CicPp.ppterm t);
   raise exn'
 in
  raise (HExtlib.Localized (loc,exn'))

let relocalize localization_tbl oldt newt =
 try
  let infos = Cic.CicHash.find localization_tbl oldt in
   Cic.CicHash.remove localization_tbl oldt;
   Cic.CicHash.add localization_tbl newt infos;
 with
  Not_found -> ()
;;
                       
let rec split l n =
 match (l,n) with
    (l,0) -> ([], l)
  | (he::tl, n) -> let (l1,l2) = split tl (n-1) in (he::l1,l2)
  | (_,_) -> raise (AssertFailure (lazy "split: list too short"))
;;

let exp_impl metasenv subst context =
 function
  | Some `Type ->
      let (metasenv', idx) = 
        CicMkImplicit.mk_implicit_type metasenv subst context in
      let irl = 
        CicMkImplicit.identity_relocation_list_for_metavariable context in
      metasenv', Cic.Meta (idx, irl)
  | Some `Closed ->
      let (metasenv', idx) = CicMkImplicit.mk_implicit metasenv subst [] in
      metasenv', Cic.Meta (idx, [])
  | None ->
      let (metasenv', idx) = CicMkImplicit.mk_implicit metasenv subst context in
      let irl = 
        CicMkImplicit.identity_relocation_list_for_metavariable context in
      metasenv', Cic.Meta (idx, irl)
  | _ -> assert false
;;

let unvariant newt =
 match newt with
 | Cic.Appl (hd::args) ->
    let uri = CicUtil.uri_of_term hd in
    (match 
      CicEnvironment.get_obj CicUniv.oblivion_ugraph uri 
    with
    | Cic.Constant (_,Some t,_,[],attrs),_ 
      when List.exists ((=) (`Flavour `Variant)) attrs -> 
       Cic.Appl (t::args)
    | _ -> newt)
 | _ -> newt
;;

let is_a_double_coercion t =
  let rec subst_nth n x l =
    match n,l with
    | _, [] -> []
    | 0, _::tl -> x :: tl
    | n, hd::tl -> hd :: subst_nth (n-1) x tl
  in
  let imp = Cic.Implicit None in
  let dummyres = false,imp, imp,imp,imp in
  match t with
  | Cic.Appl l1 ->
     (match CoercGraph.coerced_arg l1 with
     | Some (Cic.Appl l2, pos1) -> 
         (match CoercGraph.coerced_arg l2 with
         | Some (x, pos2) ->
             true, List.hd l1, List.hd l2, x,
              Cic.Appl (subst_nth (pos1 + 1) 
                (Cic.Appl (subst_nth (pos2+1) imp l2)) l1)
         | _ -> dummyres)
      | _ -> dummyres)
  | _ -> dummyres
;;

let more_args_than_expected localization_tbl metasenv subst he context hetype' residuals tlbody_and_type exn
=
  let len = List.length tlbody_and_type in
  let msg = 
    lazy ("The term " ^
      CicMetaSubst.ppterm_in_context ~metasenv subst he context ^ 
      " (that has type "^ CicMetaSubst.ppterm_in_context ~metasenv subst hetype' context ^
      ") is here applied to " ^ string_of_int len ^
      " arguments but here it can handle only up to " ^
      string_of_int (len - residuals) ^ " arguments")
  in
  enrich localization_tbl he ~f:(fun _-> msg) exn
;; 

let mk_prod_of_metas metasenv context subst args = 
  let rec mk_prod metasenv context' = function
    | [] ->
        let (metasenv, idx) = 
          CicMkImplicit.mk_implicit_type metasenv subst context'
        in
        let irl =
          CicMkImplicit.identity_relocation_list_for_metavariable context'
        in
          metasenv,Cic.Meta (idx, irl)
    | (_,argty)::tl ->
        let (metasenv, idx) = 
          CicMkImplicit.mk_implicit_type metasenv subst context' 
        in
        let irl =
          CicMkImplicit.identity_relocation_list_for_metavariable context'
        in
        let meta = Cic.Meta (idx,irl) in
        let name =
          (* The name must be fresh for context.                 *)
          (* Nevertheless, argty is well-typed only in context.  *)
          (* Thus I generate a name (name_hint) in context and   *)
          (* then I generate a name --- using the hint name_hint *)
          (* --- that is fresh in context'.                      *)
          let name_hint = 
            FreshNamesGenerator.mk_fresh_name ~subst metasenv 
              (CicMetaSubst.apply_subst_context subst context)
              Cic.Anonymous
              ~typ:(CicMetaSubst.apply_subst subst argty) 
          in
            FreshNamesGenerator.mk_fresh_name ~subst
              [] context' name_hint ~typ:(Cic.Sort Cic.Prop)
        in
        let metasenv,target =
          mk_prod metasenv ((Some (name, Cic.Decl meta))::context') tl
        in
          metasenv,Cic.Prod (name,meta,target)
  in
  mk_prod metasenv context args
;;
  
let rec type_of_constant uri ugraph =
 let module C = Cic in
 let module R = CicReduction in
 let module U = UriManager in
  let _ = CicTypeChecker.typecheck uri in
  let obj,u =
   try
    CicEnvironment.get_cooked_obj ugraph uri
   with Not_found -> assert false
  in
   match obj with
      C.Constant (_,_,ty,_,_) -> ty,u
    | C.CurrentProof (_,_,_,ty,_,_) -> ty,u
    | _ ->
       raise
        (RefineFailure 
          (lazy ("Unknown constant definition " ^  U.string_of_uri uri)))

and type_of_variable uri ugraph =
  let module C = Cic in
  let module R = CicReduction in
  let module U = UriManager in
  let _ = CicTypeChecker.typecheck uri in
  let obj,u =
   try
    CicEnvironment.get_cooked_obj ugraph uri
    with Not_found -> assert false
  in
   match obj with
      C.Variable (_,_,ty,_,_) -> ty,u
    | _ ->
        raise
         (RefineFailure
          (lazy ("Unknown variable definition " ^ UriManager.string_of_uri uri)))

and type_of_mutual_inductive_defs uri i ugraph =
  let module C = Cic in
  let module R = CicReduction in
  let module U = UriManager in
  let _ = CicTypeChecker.typecheck uri in
  let obj,u =
   try
    CicEnvironment.get_cooked_obj ugraph uri
   with Not_found -> assert false
  in
   match obj with
      C.InductiveDefinition (dl,_,_,_) ->
        let (_,_,arity,_) = List.nth dl i in
         arity,u
    | _ ->
       raise
        (RefineFailure
         (lazy ("Unknown mutual inductive definition " ^ U.string_of_uri uri)))

and type_of_mutual_inductive_constr uri i j ugraph =
  let module C = Cic in
  let module R = CicReduction in
  let module U = UriManager in
  let _ = CicTypeChecker.typecheck uri in
   let obj,u =
    try
     CicEnvironment.get_cooked_obj ugraph uri
    with Not_found -> assert false
   in
    match obj with
        C.InductiveDefinition (dl,_,_,_) ->
          let (_,_,_,cl) = List.nth dl i in
          let (_,ty) = List.nth cl (j-1) in
            ty,u
      | _ -> 
          raise
                  (RefineFailure
              (lazy 
                ("Unkown mutual inductive definition " ^ U.string_of_uri uri)))


(* type_of_aux' is just another name (with a different scope) for type_of_aux *)

(* the check_branch function checks if a branch of a case is refinable. 
   It returns a pair (outype_instance,args), a subst and a metasenv.
   outype_instance is the expected result of applying the case outtype 
   to args. 
   The problem is that outype is in general unknown, and we should
   try to synthesize it from the above information, that is in general
   a second order unification problem. *)
 
and check_branch n context metasenv subst left_args_no actualtype term expectedtype ugraph =
  let module C = Cic in
  let module R = CicReduction in
    match R.whd ~subst context expectedtype with
        C.MutInd (_,_,_) ->
          (n,context,actualtype, [term]), subst, metasenv, ugraph
      | C.Appl (C.MutInd (_,_,_)::tl) ->
          let (_,arguments) = split tl left_args_no in
            (n,context,actualtype, arguments@[term]), subst, metasenv, ugraph 
      | C.Prod (_,so,de) ->
          (* we expect that the actual type of the branch has the due 
             number of Prod *)
          (match R.whd ~subst context actualtype with
               C.Prod (name',so',de') ->
                 let subst, metasenv, ugraph1 = 
                   fo_unif_subst subst context metasenv so so' ugraph in
                 let term' =
                   (match CicSubstitution.lift 1 term with
                        C.Appl l -> C.Appl (l@[C.Rel 1])
                      | t -> C.Appl [t ; C.Rel 1]) in
                   (* we should also check that the name variable is anonymous in
                      the actual type de' ?? *)
                   check_branch (n+1) 
                     ((Some (name',(C.Decl so)))::context) 
                       metasenv subst left_args_no de' term' de ugraph1
             | _ -> raise (AssertFailure (lazy "Wrong number of arguments")))
      | _ -> raise (AssertFailure (lazy "Prod or MutInd expected"))

and type_of_aux' ?(clean_dummy_dependent_types=true) 
  ?(localization_tbl = Cic.CicHash.create 1) metasenv subst context t ugraph
=
  let rec type_of_aux subst metasenv context t ugraph =
    let module C = Cic in
    let module S = CicSubstitution in
    let module U = UriManager in
     let (t',_,_,_,_) as res =
      match t with
          (*    function *)
          C.Rel n ->
            (try
               match List.nth context (n - 1) with
                   Some (_,C.Decl ty) -> 
                     t,S.lift n ty,subst,metasenv, ugraph
                 | Some (_,C.Def (_,ty)) -> 
                     t,S.lift n ty,subst,metasenv, ugraph
                 | None ->
                    enrich localization_tbl t
                     (RefineFailure (lazy "Rel to hidden hypothesis"))
             with
              Failure _ ->
               enrich localization_tbl t
                (RefineFailure (lazy "Not a closed term")))
        | C.Var (uri,exp_named_subst) ->
            let exp_named_subst',subst',metasenv',ugraph1 =
              check_exp_named_subst 
                subst metasenv context exp_named_subst ugraph 
            in
            let ty_uri,ugraph1 = type_of_variable uri ugraph in
            let ty =
              CicSubstitution.subst_vars exp_named_subst' ty_uri
            in
              C.Var (uri,exp_named_subst'),ty,subst',metasenv',ugraph1
        | C.Meta (n,l) -> 
            (try
               let (canonical_context, term,ty) = 
                 CicUtil.lookup_subst n subst 
               in
               let l',subst',metasenv',ugraph1 =
                 check_metasenv_consistency n subst metasenv context
                   canonical_context l ugraph 
               in
                 (* trust or check ??? *)
                 C.Meta (n,l'),CicSubstitution.subst_meta l' ty, 
                   subst', metasenv', ugraph1
                   (* type_of_aux subst metasenv 
                      context (CicSubstitution.subst_meta l term) *)
             with CicUtil.Subst_not_found _ ->
               let (_,canonical_context,ty) = CicUtil.lookup_meta n metasenv in
               let l',subst',metasenv', ugraph1 =
                 check_metasenv_consistency n subst metasenv context
                   canonical_context l ugraph
               in
                 C.Meta (n,l'),CicSubstitution.subst_meta l' ty, 
                   subst', metasenv',ugraph1)
        | C.Sort (C.Type tno) -> 
            let tno' = CicUniv.fresh() in 
             (try
               let ugraph1 = CicUniv.add_gt tno' tno ugraph in
                 t,(C.Sort (C.Type tno')),subst,metasenv,ugraph1
              with
               CicUniv.UniverseInconsistency msg -> raise (RefineFailure msg))
        | C.Sort (C.CProp tno) -> 
            let tno' = CicUniv.fresh() in 
             (try
               let ugraph1 = CicUniv.add_gt tno' tno ugraph in
                 t,(C.Sort (C.Type tno')),subst,metasenv,ugraph1
              with
               CicUniv.UniverseInconsistency msg -> raise (RefineFailure msg))
        | C.Sort (C.Prop|C.Set) -> 
            t,C.Sort (C.Type (CicUniv.fresh())),subst,metasenv,ugraph
        | C.Implicit infos ->
           let metasenv',t' = exp_impl metasenv subst context infos in
            type_of_aux subst metasenv' context t' ugraph
        | C.Cast (te,ty) ->
            let ty',_,subst',metasenv',ugraph1 =
              type_of_aux subst metasenv context ty ugraph 
            in
            let te',inferredty,subst'',metasenv'',ugraph2 =
              type_of_aux subst' metasenv' context te ugraph1
            in
            let rec count_prods context ty =
              match CicReduction.whd context ~subst:subst'' ty with
              | Cic.Prod (n,s,t) -> 
                 1 + count_prods (Some (n,Cic.Decl s)::context) t
              | _ -> 0
            in
            let exp_prods = count_prods context ty' in
            let inf_prods = count_prods context inferredty in
            let te', inferredty, metasenv'', subst'', ugraph2 =
               let rec aux t m s ug it = function
                 | 0 -> t,it,m,s,ug
                 | n ->
                      match CicReduction.whd context ~subst:s it with
                      | Cic.Prod (_,src,tgt) -> 
                          let newmeta, metaty, s, m, ug =
                            type_of_aux s m context (Cic.Implicit None) ug
                          in
                          let s,m,ug = 
                            fo_unif_subst s context m metaty src ug
                          in
                          let t =
                            match t with
                            | Cic.Appl l -> Cic.Appl (l @ [newmeta])
                            | _ -> Cic.Appl [t;newmeta]
                          in
                          aux t m s ug (CicSubstitution.subst newmeta tgt) (n-1)
                      | _ -> t,it,m,s,ug     
               in
                 aux te' metasenv'' subst'' ugraph2 inferredty
                   (max 0 (inf_prods - exp_prods))
            in
            let (te', ty'), subst''',metasenv''',ugraph3 =
              coerce_to_something true localization_tbl te' inferredty ty'
                subst'' metasenv'' context ugraph2
            in
             C.Cast (te',ty'),ty',subst''',metasenv''',ugraph3
        | C.Prod (name,s,t) ->
            let s',sort1,subst',metasenv',ugraph1 = 
              type_of_aux subst metasenv context s ugraph 
            in
            let s',sort1,subst', metasenv',ugraph1 = 
              coerce_to_sort localization_tbl 
              s' sort1 subst' context metasenv' ugraph1
            in
            let context_for_t = ((Some (name,(C.Decl s')))::context) in
            let t',sort2,subst'',metasenv'',ugraph2 =
              type_of_aux subst' metasenv' 
                context_for_t t ugraph1
            in
            let t',sort2,subst'',metasenv'',ugraph2 = 
              coerce_to_sort localization_tbl 
              t' sort2 subst'' context_for_t metasenv'' ugraph2
            in
              let sop,subst''',metasenv''',ugraph3 =
                sort_of_prod localization_tbl subst'' metasenv'' 
                  context (name,s') t' (sort1,sort2) ugraph2
              in
                C.Prod (name,s',t'),sop,subst''',metasenv''',ugraph3
        | C.Lambda (n,s,t) ->
            let s',sort1,subst',metasenv',ugraph1 = 
              type_of_aux subst metasenv context s ugraph 
            in
            let s',sort1,subst',metasenv',ugraph1 =
              coerce_to_sort localization_tbl 
              s' sort1 subst' context metasenv' ugraph1
            in
            let context_for_t = ((Some (n,(C.Decl s')))::context) in 
            let t',type2,subst'',metasenv'',ugraph2 =
              type_of_aux subst' metasenv' context_for_t t ugraph1
            in
              C.Lambda (n,s',t'),C.Prod (n,s',type2),
                subst'',metasenv'',ugraph2
        | C.LetIn (n,s,ty,t) ->
           (* only to check if s is well-typed *)
           let s',ty',subst',metasenv',ugraph1 = 
             type_of_aux subst metasenv context s ugraph in
           let ty,_,subst',metasenv',ugraph1 =
             type_of_aux subst' metasenv' context ty ugraph1 in
           let subst',metasenv',ugraph1 =
            try
             fo_unif_subst subst' context metasenv'
               ty ty' ugraph1
            with
             exn ->
              enrich localization_tbl s' exn
               ~f:(function _ ->
                 lazy ("(2) The term " ^
                  CicMetaSubst.ppterm_in_context ~metasenv:metasenv' subst' s'
                   context ^ " has type " ^
                  CicMetaSubst.ppterm_in_context ~metasenv:metasenv' subst' ty'
                   context ^ " but is here used with type " ^
                  CicMetaSubst.ppterm_in_context ~metasenv:metasenv' subst' ty
                   context))
           in
           let context_for_t = ((Some (n,(C.Def (s',ty))))::context) in
           
            let t',inferredty,subst'',metasenv'',ugraph2 =
              type_of_aux subst' metasenv' 
                context_for_t t ugraph1
            in
              (* One-step LetIn reduction. 
               * Even faster than the previous solution.
               * Moreover the inferred type is closer to the expected one. 
               *)
              C.LetIn (n,s',ty,t'),
               CicSubstitution.subst ~avoid_beta_redexes:true s' inferredty,
               subst'',metasenv'',ugraph2
        | C.Appl (he::((_::_) as tl)) ->
            let he',hetype,subst',metasenv',ugraph1 = 
              type_of_aux subst metasenv context he ugraph 
            in
            let tlbody_and_type,subst'',metasenv'',ugraph2 =
               typeof_list subst' metasenv' context ugraph1 tl
            in
            let coerced_he,coerced_args,applty,subst''',metasenv''',ugraph3 =
              eat_prods true subst'' metasenv'' context 
                he' hetype tlbody_and_type ugraph2
            in
            let newappl = (C.Appl (coerced_he::coerced_args)) in
            avoid_double_coercion 
              context subst''' metasenv''' ugraph3 newappl applty
        | C.Appl _ -> assert false
        | C.Const (uri,exp_named_subst) ->
            let exp_named_subst',subst',metasenv',ugraph1 =
              check_exp_named_subst subst metasenv context 
                exp_named_subst ugraph in
            let ty_uri,ugraph2 = type_of_constant uri ugraph1 in
            let cty =
              CicSubstitution.subst_vars exp_named_subst' ty_uri
            in
              C.Const (uri,exp_named_subst'),cty,subst',metasenv',ugraph2
        | C.MutInd (uri,i,exp_named_subst) ->
            let exp_named_subst',subst',metasenv',ugraph1 =
              check_exp_named_subst subst metasenv context 
                exp_named_subst ugraph 
            in
            let ty_uri,ugraph2 = type_of_mutual_inductive_defs uri i ugraph1 in
            let cty =
              CicSubstitution.subst_vars exp_named_subst' ty_uri in
              C.MutInd (uri,i,exp_named_subst'),cty,subst',metasenv',ugraph2
        | C.MutConstruct (uri,i,j,exp_named_subst) ->
            let exp_named_subst',subst',metasenv',ugraph1 =
              check_exp_named_subst subst metasenv context 
                exp_named_subst ugraph 
            in
            let ty_uri,ugraph2 = 
              type_of_mutual_inductive_constr uri i j ugraph1 
            in
            let cty =
              CicSubstitution.subst_vars exp_named_subst' ty_uri 
            in
              C.MutConstruct (uri,i,j,exp_named_subst'),cty,subst',
                metasenv',ugraph2
        | C.MutCase (uri, i, outtype, term, pl) ->
            (* first, get the inductive type (and noparams) 
             * in the environment  *)
            let (_,b,arity,constructors), expl_params, no_left_params,ugraph =
              let _ = CicTypeChecker.typecheck uri in
              let obj,u = CicEnvironment.get_cooked_obj ugraph uri in
              match obj with
                  C.InductiveDefinition (l,expl_params,parsno,_) -> 
                    List.nth l i , expl_params, parsno, u
                | _ ->
                    enrich localization_tbl t
                     (RefineFailure
                       (lazy ("Unkown mutual inductive definition " ^ 
                         U.string_of_uri uri)))
           in
           if List.length constructors <> List.length pl then
            enrich localization_tbl t
             (RefineFailure
               (lazy "Wrong number of cases")) ;
           let rec count_prod t =
             match CicReduction.whd ~subst context t with
                 C.Prod (_, _, t) -> 1 + (count_prod t)
               | _ -> 0 
           in 
           let no_args = count_prod arity in
             (* now, create a "generic" MutInd *)
           let metasenv,left_args = 
             CicMkImplicit.n_fresh_metas metasenv subst context no_left_params
           in
           let metasenv,right_args = 
             let no_right_params = no_args - no_left_params in
               if no_right_params < 0 then assert false
               else CicMkImplicit.n_fresh_metas 
                      metasenv subst context no_right_params 
           in
           let metasenv,exp_named_subst = 
             CicMkImplicit.fresh_subst metasenv subst context expl_params in
           let expected_type = 
             if no_args = 0 then 
               C.MutInd (uri,i,exp_named_subst)
             else
               C.Appl 
                 (C.MutInd (uri,i,exp_named_subst)::(left_args @ right_args))
           in
             (* check consistency with the actual type of term *)
           let term',actual_type,subst,metasenv,ugraph1 = 
             type_of_aux subst metasenv context term ugraph in
           let expected_type',_, subst, metasenv,ugraph2 =
             type_of_aux subst metasenv context expected_type ugraph1
           in
           let actual_type = CicReduction.whd ~subst context actual_type in
           let subst,metasenv,ugraph3 =
            try
             fo_unif_subst subst context metasenv 
               expected_type' actual_type ugraph2
            with
             exn ->
              enrich localization_tbl term' exn
               ~f:(function _ ->
                 lazy ("(3) The term " ^
                  CicMetaSubst.ppterm_in_context ~metasenv subst term'
                   context ^ " has type " ^
                  CicMetaSubst.ppterm_in_context ~metasenv subst actual_type
                   context ^ " but is here used with type " ^
                  CicMetaSubst.ppterm_in_context ~metasenv subst expected_type'
                  context))
           in
           let rec instantiate_prod t =
            function
               [] -> t
             | he::tl ->
                match CicReduction.whd ~subst context t with
                   C.Prod (_,_,t') ->
                    instantiate_prod (CicSubstitution.subst he t') tl
                 | _ -> assert false
           in
           let arity_instantiated_with_left_args =
            instantiate_prod arity left_args in
             (* TODO: check if the sort elimination 
              * is allowed: [(I q1 ... qr)|B] *)
           let (pl',_,outtypeinstances,subst,metasenv,ugraph4) =
             List.fold_right
               (fun p (pl,j,outtypeinstances,subst,metasenv,ugraph) ->
                  let constructor =
                    if left_args = [] then
                      (C.MutConstruct (uri,i,j,exp_named_subst))
                    else
                      (C.Appl 
                        (C.MutConstruct (uri,i,j,exp_named_subst)::left_args))
                  in
                  let p',actual_type,subst,metasenv,ugraph1 = 
                    type_of_aux subst metasenv context p ugraph 
                  in
                  let constructor',expected_type, subst, metasenv,ugraph2 = 
                    type_of_aux subst metasenv context constructor ugraph1 
                  in
                  let outtypeinstance,subst,metasenv,ugraph3 =
                   try
                    check_branch 0 context metasenv subst
                     no_left_params actual_type constructor' expected_type
                     ugraph2 
                   with
                    exn ->
                     enrich localization_tbl constructor'
                      ~f:(fun _ ->
                        lazy ("(4) The term " ^
                         CicMetaSubst.ppterm_in_context metasenv subst p'
                          context ^ " has type " ^
                         CicMetaSubst.ppterm_in_context metasenv subst actual_type
                          context ^ " but is here used with type " ^
                         CicMetaSubst.ppterm_in_context metasenv subst expected_type
                          context)) exn
                  in
                    (p'::pl,j-1,
                     outtypeinstance::outtypeinstances,subst,metasenv,ugraph3))
               pl ([],List.length pl,[],subst,metasenv,ugraph3)
           in
           
             (* we are left to check that the outype matches his instances.
                The easy case is when the outype is specified, that amount
                to a trivial check. Otherwise, we should guess a type from
                its instances 
             *)
             
           let outtype,outtypety, subst, metasenv,ugraph4 =
             type_of_aux subst metasenv context outtype ugraph4 in
           (match outtype with
           | C.Meta (n,l) ->
               (let candidate,ugraph5,metasenv,subst = 
                 let exp_name_subst, metasenv = 
                    let o,_ = 
                      CicEnvironment.get_cooked_obj CicUniv.oblivion_ugraph uri 
                    in
                    let uris = CicUtil.params_of_obj o in
                    List.fold_right (
                      fun uri (acc,metasenv) -> 
                        let metasenv',new_meta = 
                           CicMkImplicit.mk_implicit metasenv subst context
                        in
                        let irl =
                          CicMkImplicit.identity_relocation_list_for_metavariable 
                            context
                        in
                        (uri, Cic.Meta(new_meta,irl))::acc, metasenv'
                    ) uris ([],metasenv)
                 in
                 let ty =
                  match left_args,right_args with
                     [],[] -> Cic.MutInd(uri, i, exp_name_subst)
                   | _,_ ->
                      let rec mk_right_args =
                       function
                          0 -> []
                        | n -> (Cic.Rel n)::(mk_right_args (n - 1))
                      in
                      let right_args_no = List.length right_args in
                      let lifted_left_args =
                       List.map (CicSubstitution.lift right_args_no) left_args
                      in
                       Cic.Appl (Cic.MutInd(uri,i,exp_name_subst)::
                        (lifted_left_args @ mk_right_args right_args_no))
                 in
                 let fresh_name = 
                   FreshNamesGenerator.mk_fresh_name ~subst metasenv 
                     context Cic.Anonymous ~typ:ty
                 in
                 match outtypeinstances with
                 | [] -> 
                     let extended_context = 
                      let rec add_right_args =
                       function
                          Cic.Prod (name,ty,t) ->
                           Some (name,Cic.Decl ty)::(add_right_args t)
                        | _ -> []
                      in
                       (Some (fresh_name,Cic.Decl ty))::
                       (List.rev
                        (add_right_args arity_instantiated_with_left_args))@
                       context
                     in
                     let metasenv,new_meta = 
                       CicMkImplicit.mk_implicit metasenv subst extended_context
                     in
                       let irl =
                       CicMkImplicit.identity_relocation_list_for_metavariable 
                         extended_context
                     in
                     let rec add_lambdas b =
                      function
                         Cic.Prod (name,ty,t) ->
                          Cic.Lambda (name,ty,(add_lambdas b t))
                       | _ -> Cic.Lambda (fresh_name, ty, b)
                     in
                     let candidate = 
                      add_lambdas (Cic.Meta (new_meta,irl))
                       arity_instantiated_with_left_args
                     in
                     (Some candidate),ugraph4,metasenv,subst
                 | (constructor_args_no,_,instance,_)::tl -> 
                     try
                       let instance',subst,metasenv = 
                         CicMetaSubst.delift_rels subst metasenv
                          constructor_args_no instance
                       in
                       let candidate,ugraph,metasenv,subst =
                         List.fold_left (
                           fun (candidate_oty,ugraph,metasenv,subst) 
                             (constructor_args_no,_,instance,_) ->
                               match candidate_oty with
                               | None -> None,ugraph,metasenv,subst
                               | Some ty ->
                                 try 
                                   let instance',subst,metasenv = 
                                     CicMetaSubst.delift_rels subst metasenv
                                      constructor_args_no instance
                                   in
                                   let subst,metasenv,ugraph =
                                    fo_unif_subst subst context metasenv 
                                      instance' ty ugraph
                                   in
                                    candidate_oty,ugraph,metasenv,subst
                                 with
                                    CicMetaSubst.DeliftingARelWouldCaptureAFreeVariable
                                  | RefineFailure _ | Uncertain _ ->
                                     None,ugraph,metasenv,subst
                         ) (Some instance',ugraph4,metasenv,subst) tl
                       in
                       match candidate with
                       | None -> None, ugraph,metasenv,subst
                       | Some t -> 
                          let rec add_lambdas n b =
                           function
                              Cic.Prod (name,ty,t) ->
                               Cic.Lambda (name,ty,(add_lambdas (n + 1) b t))
                            | _ ->
                              Cic.Lambda (fresh_name, ty,
                               CicSubstitution.lift (n + 1) t)
                          in
                           Some
                            (add_lambdas 0 t arity_instantiated_with_left_args),
                           ugraph,metasenv,subst
                     with CicMetaSubst.DeliftingARelWouldCaptureAFreeVariable ->
                       None,ugraph4,metasenv,subst
               in
               match candidate with
               | None -> raise (Uncertain (lazy "can't solve an higher order unification problem"))
               | Some candidate ->
                   let subst,metasenv,ugraph = 
                    try
                     fo_unif_subst subst context metasenv 
                       candidate outtype ugraph5
                    with
                     exn -> assert false(* unification against a metavariable *)
                   in
                     C.MutCase (uri, i, outtype, term', pl'),
                      CicReduction.head_beta_reduce
                       (CicMetaSubst.apply_subst subst
                        (Cic.Appl (outtype::right_args@[term']))),
                     subst,metasenv,ugraph)
           | _ ->    (* easy case *)
             let tlbody_and_type,subst,metasenv,ugraph4 =
               typeof_list subst metasenv context ugraph4 (right_args @ [term'])
             in
             let _,_,_,subst,metasenv,ugraph4 =
               eat_prods false subst metasenv context 
                 outtype outtypety tlbody_and_type ugraph4
             in
             let _,_, subst, metasenv,ugraph5 =
               type_of_aux subst metasenv context
                 (C.Appl ((outtype :: right_args) @ [term'])) ugraph4
             in
             let (subst,metasenv,ugraph6) = 
               List.fold_left2
                 (fun (subst,metasenv,ugraph) 
                   p (constructor_args_no,context,instance,args)
                  ->
                    let instance' = 
                      let appl =
                        let outtype' =
                          CicSubstitution.lift constructor_args_no outtype
                        in
                          C.Appl (outtype'::args)
                      in
                        CicReduction.head_beta_reduce ~delta:false 
                          ~upto:(List.length args) appl 
                    in
                     try
                      fo_unif_subst subst context metasenv instance instance'
                       ugraph
                     with
                      exn ->
                       enrich localization_tbl p exn
                        ~f:(function _ ->
                          lazy ("(5) The term " ^
                           CicMetaSubst.ppterm_in_context ~metasenv subst p
                            context ^ " has type " ^
                           CicMetaSubst.ppterm_in_context ~metasenv subst instance'
                            context ^ " but is here used with type " ^
                           CicMetaSubst.ppterm_in_context ~metasenv subst instance
                            context)))
                 (subst,metasenv,ugraph5) pl' outtypeinstances
             in
               C.MutCase (uri, i, outtype, term', pl'),
                 CicReduction.head_beta_reduce
                  (CicMetaSubst.apply_subst subst
                   (C.Appl(outtype::right_args@[term']))),
                 subst,metasenv,ugraph6)
        | C.Fix (i,fl) ->
            let fl_ty',subst,metasenv,types,ugraph1,len =
              List.fold_left
                (fun (fl,subst,metasenv,types,ugraph,len) (n,_,ty,_) ->
                   let ty',_,subst',metasenv',ugraph1 = 
                      type_of_aux subst metasenv context ty ugraph 
                   in
                     fl @ [ty'],subst',metasenv', 
                       Some (C.Name n,(C.Decl (CicSubstitution.lift len ty')))
                        :: types, ugraph, len+1
                ) ([],subst,metasenv,[],ugraph,0) fl
            in
            let context' = types@context in
            let fl_bo',subst,metasenv,ugraph2 =
              List.fold_left
                (fun (fl,subst,metasenv,ugraph) ((name,x,_,bo),ty) ->
                   let bo',ty_of_bo,subst,metasenv,ugraph1 =
                     type_of_aux subst metasenv context' bo ugraph in
                   let expected_ty = CicSubstitution.lift len ty in
                   let subst',metasenv',ugraph' =
                    try
                     fo_unif_subst subst context' metasenv
                       ty_of_bo expected_ty ugraph1
                    with
                     exn ->
                      enrich localization_tbl bo exn
                       ~f:(function _ ->
                         lazy ("(7) The term " ^
                          CicMetaSubst.ppterm_in_context ~metasenv subst bo
                           context' ^ " has type " ^
                          CicMetaSubst.ppterm_in_context ~metasenv subst ty_of_bo
                           context' ^ " but is here used with type " ^
                          CicMetaSubst.ppterm_in_context ~metasenv subst expected_ty
                           context'))
                   in 
                     fl @ [bo'] , subst',metasenv',ugraph'
                ) ([],subst,metasenv,ugraph1) (List.combine fl fl_ty') 
            in
            let ty = List.nth fl_ty' i in
            (* now we have the new ty in fl_ty', the new bo in fl_bo',
             * and we want the new fl with bo' and ty' injected in the right
             * place.
             *) 
            let rec map3 f l1 l2 l3 =
              match l1,l2,l3 with
              | [],[],[] -> []
              | h1::tl1,h2::tl2,h3::tl3 -> (f h1 h2 h3) :: (map3 f tl1 tl2 tl3)
              | _ -> assert false 
            in
            let fl'' = map3 (fun ty' bo' (name,x,ty,bo) -> (name,x,ty',bo') ) 
              fl_ty' fl_bo' fl 
            in
              C.Fix (i,fl''),ty,subst,metasenv,ugraph2
        | C.CoFix (i,fl) ->
            let fl_ty',subst,metasenv,types,ugraph1,len =
              List.fold_left
                (fun (fl,subst,metasenv,types,ugraph,len) (n,ty,_) ->
                   let ty',_,subst',metasenv',ugraph1 = 
                     type_of_aux subst metasenv context ty ugraph 
                   in
                     fl @ [ty'],subst',metasenv', 
                      Some (C.Name n,(C.Decl (CicSubstitution.lift len ty'))) ::
                        types, ugraph1, len+1
                ) ([],subst,metasenv,[],ugraph,0) fl
            in
            let context' = types@context in
            let fl_bo',subst,metasenv,ugraph2 =
              List.fold_left
                (fun (fl,subst,metasenv,ugraph) ((name,_,bo),ty) ->
                   let bo',ty_of_bo,subst,metasenv,ugraph1 =
                     type_of_aux subst metasenv context' bo ugraph in
                   let expected_ty = CicSubstitution.lift len ty in
                   let subst',metasenv',ugraph' = 
                    try
                     fo_unif_subst subst context' metasenv
                       ty_of_bo expected_ty ugraph1
                    with
                     exn ->
                      enrich localization_tbl bo exn
                       ~f:(function _ ->
                         lazy ("(8) The term " ^
                          CicMetaSubst.ppterm_in_context ~metasenv subst bo
                           context' ^ " has type " ^
                          CicMetaSubst.ppterm_in_context ~metasenv subst ty_of_bo
                           context' ^ " but is here used with type " ^
                          CicMetaSubst.ppterm_in_context ~metasenv subst expected_ty
                           context))
                   in
                     fl @ [bo'],subst',metasenv',ugraph'
                ) ([],subst,metasenv,ugraph1) (List.combine fl fl_ty')
            in
            let ty = List.nth fl_ty' i in
            (* now we have the new ty in fl_ty', the new bo in fl_bo',
             * and we want the new fl with bo' and ty' injected in the right
             * place.
             *) 
            let rec map3 f l1 l2 l3 =
              match l1,l2,l3 with
              | [],[],[] -> []
              | h1::tl1,h2::tl2,h3::tl3 -> (f h1 h2 h3) :: (map3 f tl1 tl2 tl3)
              | _ -> assert false
            in
            let fl'' = map3 (fun ty' bo' (name,ty,bo) -> (name,ty',bo') ) 
              fl_ty' fl_bo' fl 
            in
              C.CoFix (i,fl''),ty,subst,metasenv,ugraph2
     in
      relocalize localization_tbl t t';
      res

  (* check_metasenv_consistency checks that the "canonical" context of a
     metavariable is consitent - up to relocation via the relocation list l -
     with the actual context *)
  and check_metasenv_consistency
    metano subst metasenv context canonical_context l ugraph
    =
    let module C = Cic in
    let module R = CicReduction in
    let module S = CicSubstitution in
    let lifted_canonical_context = 
      let rec aux i =
        function
            [] -> []
          | (Some (n,C.Decl t))::tl ->
              (Some (n,C.Decl (S.subst_meta l (S.lift i t))))::(aux (i+1) tl)
          | None::tl -> None::(aux (i+1) tl)
          | (Some (n,C.Def (t,ty)))::tl ->
              (Some
               (n,
                C.Def
                 (S.subst_meta l (S.lift i t),
                  S.subst_meta l (S.lift i ty)))) :: (aux (i+1) tl)
      in
        aux 1 canonical_context 
    in
      try
        List.fold_left2 
          (fun (l,subst,metasenv,ugraph) t ct -> 
             match (t,ct) with
                 _,None ->
                   l @ [None],subst,metasenv,ugraph
               | Some t,Some (_,C.Def (ct,_)) ->
                  (*CSC: the following optimization is to avoid a possibly
                         expensive reduction that can be easily avoided and
                         that is quite frequent. However, this is better
                         handled using levels to control reduction *)
                  let optimized_t =
                   match t with
                      Cic.Rel n ->
                       (try
                         match List.nth context (n - 1) with
                            Some (_,C.Def (te,_)) -> S.lift n te
                          | _ -> t
                        with
                         Failure _ -> t)
                    | _ -> t
                  in
                   let subst',metasenv',ugraph' = 
                   (try
(*prerr_endline ("poco geniale: nel caso di IRL basterebbe sapere che questo e'
 * il Rel corrispondente. Si puo' ottimizzare il caso t = rel.");*)
                      fo_unif_subst subst context metasenv optimized_t ct ugraph
                    with e -> raise (RefineFailure (lazy (sprintf "The local context is not consistent with the canonical context, since %s cannot be unified with %s. Reason: %s" (CicMetaSubst.ppterm ~metasenv subst optimized_t) (CicMetaSubst.ppterm ~metasenv subst ct) (match e with AssertFailure msg -> Lazy.force msg | _ -> (Printexc.to_string e))))))
                   in
                     l @ [Some t],subst',metasenv',ugraph'
               | Some t,Some (_,C.Decl ct) ->
                   let t',inferredty,subst',metasenv',ugraph1 =
                     type_of_aux subst metasenv context t ugraph
                   in
                   let subst'',metasenv'',ugraph2 = 
                     (try
                        fo_unif_subst
                          subst' context metasenv' inferredty ct ugraph1
                      with e -> raise (RefineFailure (lazy (sprintf "The local context is not consistent with the canonical context, since the type %s of %s cannot be unified with the expected type %s. Reason: %s" (CicMetaSubst.ppterm metasenv' subst' inferredty) (CicMetaSubst.ppterm metasenv' subst' t) (CicMetaSubst.ppterm metasenv' subst' ct) (match e with AssertFailure msg -> Lazy.force msg | RefineFailure msg -> Lazy.force msg | _ -> (Printexc.to_string e))))))
                   in
                     l @ [Some t'], subst'',metasenv'',ugraph2
               | None, Some _  ->
                   raise (RefineFailure (lazy (sprintf "Not well typed metavariable instance %s: the local context does not instantiate an hypothesis even if the hypothesis is not restricted in the canonical context %s" (CicMetaSubst.ppterm ~metasenv subst (Cic.Meta (metano, l))) (CicMetaSubst.ppcontext ~metasenv subst canonical_context))))) ([],subst,metasenv,ugraph) l lifted_canonical_context 
      with
          Invalid_argument _ ->
            raise
            (RefineFailure
               (lazy (sprintf
                  "Not well typed metavariable instance %s: the length of the local context does not match the length of the canonical context %s"
                  (CicMetaSubst.ppterm ~metasenv subst (Cic.Meta (metano, l)))
                  (CicMetaSubst.ppcontext ~metasenv subst canonical_context))))

  and check_exp_named_subst metasubst metasenv context tl ugraph =
    let rec check_exp_named_subst_aux metasubst metasenv substs tl ugraph  =
      match tl with
          [] -> [],metasubst,metasenv,ugraph
        | (uri,t)::tl ->
            let ty_uri,ugraph1 =  type_of_variable uri ugraph in
            let typeofvar =
              CicSubstitution.subst_vars substs ty_uri in
              (* CSC: why was this code here? it is wrong
                 (match CicEnvironment.get_cooked_obj ~trust:false uri with
                 Cic.Variable (_,Some bo,_,_) ->
                 raise
                 (RefineFailure (lazy
                 "A variable with a body can not be explicit substituted"))
                 | Cic.Variable (_,None,_,_) -> ()
                 | _ ->
                 raise
                 (RefineFailure (lazy
                 ("Unkown variable definition " ^ UriManager.string_of_uri uri)))
                 ) ;
              *)
            let t',typeoft,metasubst',metasenv',ugraph2 =
              type_of_aux metasubst metasenv context t ugraph1 in
            let subst = uri,t' in
            let metasubst'',metasenv'',ugraph3 =
              try
                fo_unif_subst 
                  metasubst' context metasenv' typeoft typeofvar ugraph2
              with _ ->
                raise (RefineFailure (lazy
                         ("Wrong Explicit Named Substitution: " ^ 
                           CicMetaSubst.ppterm metasenv' metasubst' typeoft ^
                          " not unifiable with " ^ 
                          CicMetaSubst.ppterm metasenv' metasubst' typeofvar)))
            in
            (* FIXME: no mere tail recursive! *)
            let exp_name_subst, metasubst''', metasenv''', ugraph4 = 
              check_exp_named_subst_aux 
                metasubst'' metasenv'' (substs@[subst]) tl ugraph3
            in
              ((uri,t')::exp_name_subst), metasubst''', metasenv''', ugraph4
    in
      check_exp_named_subst_aux metasubst metasenv [] tl ugraph


  and sort_of_prod localization_tbl subst metasenv context (name,s) t (t1, t2)
   ugraph
  =
    let module C = Cic in
    let context_for_t2 = (Some (name,C.Decl s))::context in
    let t1'' = CicReduction.whd ~subst context t1 in
    let t2'' = CicReduction.whd ~subst context_for_t2 t2 in
      match (t1'', t2'') with
        | (C.Sort s1, C.Sort s2) when (s2 = C.Prop || s2 = C.Set) -> 
              (* different than Coq manual!!! *)
              C.Sort s2,subst,metasenv,ugraph
        | (C.Sort (C.Type t1), C.Sort (C.Type t2)) -> 
            let t' = CicUniv.fresh() in 
             (try
              let ugraph1 = CicUniv.add_ge t' t1 ugraph in
              let ugraph2 = CicUniv.add_ge t' t2 ugraph1 in
                C.Sort (C.Type t'),subst,metasenv,ugraph2
              with
               CicUniv.UniverseInconsistency msg -> raise (RefineFailure msg))
        | (C.Sort (C.CProp t1), C.Sort (C.CProp t2)) -> 
            let t' = CicUniv.fresh() in 
             (try
              let ugraph1 = CicUniv.add_ge t' t1 ugraph in
              let ugraph2 = CicUniv.add_ge t' t2 ugraph1 in
                C.Sort (C.CProp t'),subst,metasenv,ugraph2
              with
               CicUniv.UniverseInconsistency msg -> raise (RefineFailure msg))
        | (C.Sort (C.Type t1), C.Sort (C.CProp t2)) -> 
            let t' = CicUniv.fresh() in 
             (try
              let ugraph1 = CicUniv.add_ge t' t1 ugraph in
              let ugraph2 = CicUniv.add_ge t' t2 ugraph1 in
                C.Sort (C.CProp t'),subst,metasenv,ugraph2
              with
               CicUniv.UniverseInconsistency msg -> raise (RefineFailure msg))
        | (C.Sort (C.CProp t1), C.Sort (C.Type t2)) -> 
            let t' = CicUniv.fresh() in 
             (try
              let ugraph1 = CicUniv.add_ge t' t1 ugraph in
              let ugraph2 = CicUniv.add_ge t' t2 ugraph1 in
                C.Sort (C.Type t'),subst,metasenv,ugraph2
              with
               CicUniv.UniverseInconsistency msg -> raise (RefineFailure msg))
        | (C.Sort _,C.Sort (C.Type t1)) -> 
            C.Sort (C.Type t1),subst,metasenv,ugraph
        | (C.Sort _,C.Sort (C.CProp t1)) -> 
            C.Sort (C.CProp t1),subst,metasenv,ugraph
        | (C.Meta _, C.Sort _) -> t2'',subst,metasenv,ugraph
        | (C.Sort _,C.Meta _) | (C.Meta _,C.Meta _) ->
            (* TODO how can we force the meta to become a sort? If we don't we
             * break the invariant that refine produce only well typed terms *)
            (* TODO if we check the non meta term and if it is a sort then we
             * are likely to know the exact value of the result e.g. if the rhs
             * is a Sort (Prop | Set | CProp) then the result is the rhs *)
            let (metasenv,idx) =
              CicMkImplicit.mk_implicit_sort metasenv subst in
            let (subst, metasenv,ugraph1) =
             try
              fo_unif_subst subst context_for_t2 metasenv 
                (C.Meta (idx,[])) t2'' ugraph
             with _ -> assert false (* unification against a metavariable *)
            in
              t2'',subst,metasenv,ugraph1
        | (C.Sort _,_)
        | (C.Meta _,_) -> 
            enrich localization_tbl s
             (RefineFailure 
               (lazy 
                 (sprintf
                   "%s is supposed to be a type, but its type is %s"
               (CicMetaSubst.ppterm_in_context ~metasenv subst t context)
               (CicMetaSubst.ppterm_in_context ~metasenv subst t2 context))))
        | _,_ -> 
            enrich localization_tbl t
             (RefineFailure 
               (lazy 
                 (sprintf
                   "%s is supposed to be a type, but its type is %s"
               (CicMetaSubst.ppterm_in_context ~metasenv subst s context)
               (CicMetaSubst.ppterm_in_context ~metasenv subst t1 context))))

  and avoid_double_coercion context subst metasenv ugraph t ty = 
   if not !pack_coercions then
    t,ty,subst,metasenv,ugraph
   else
    let b, c1, c2, head, c1_c2_implicit = is_a_double_coercion t in
    if b then
      let source_carr = CoercGraph.source_of c2 in
      let tgt_carr = CicMetaSubst.apply_subst subst ty in
      (match CoercGraph.look_for_coercion metasenv subst context source_carr tgt_carr 
      with
      | CoercGraph.SomeCoercion candidates -> 
         let selected =
           HExtlib.list_findopt
             (fun (metasenv,last,c) _ ->
               let subst,metasenv,ugraph =
                fo_unif_subst subst context metasenv last head ugraph in
               debug_print (lazy ("\nprovo" ^ CicPp.ppterm c));
               (try
                 debug_print 
                   (lazy 
                     ("packing: " ^ 
                       CicPp.ppterm t ^ " ==> " ^ CicPp.ppterm c));
                 let newt,_,subst,metasenv,ugraph = 
                   type_of_aux subst metasenv context c ugraph in
                 debug_print (lazy "tipa...");
                 let subst, metasenv, ugraph =
                   (* COME MAI C'ERA UN IF su !pack_coercions ??? *)
                    fo_unif_subst subst context metasenv newt t ugraph
                 in
                 debug_print (lazy "unifica...");
                 Some (newt, ty, subst, metasenv, ugraph)
               with 
               | RefineFailure s | Uncertain s when not !pack_coercions-> 
                   debug_print s; debug_print (lazy "stop\n");None
               | RefineFailure s | Uncertain s -> 
                   debug_print s;debug_print (lazy "goon\n");
                   try 
                     let old_pack_coercions = !pack_coercions in
                     pack_coercions := false; (* to avoid diverging *)
                     let refined_c1_c2_implicit,ty,subst,metasenv,ugraph =
                       type_of_aux subst metasenv context c1_c2_implicit ugraph 
                     in
                     pack_coercions := old_pack_coercions;
                     let b, _, _, _, _ = 
                       is_a_double_coercion refined_c1_c2_implicit 
                     in 
                     if b then 
                       None 
                     else
                       let head' = 
                         match refined_c1_c2_implicit with
                         | Cic.Appl l -> HExtlib.list_last l
                         | _ -> assert false   
                       in
                       let subst, metasenv, ugraph =
                        try fo_unif_subst subst context metasenv 
                          head head' ugraph
                        with RefineFailure s| Uncertain s-> 
                          debug_print s;assert false 
                       in
                       let subst, metasenv, ugraph =
                         fo_unif_subst subst context metasenv 
                          refined_c1_c2_implicit t ugraph
                       in
                       Some (refined_c1_c2_implicit,ty,subst,metasenv,ugraph)
                   with 
                   | RefineFailure s | Uncertain s -> 
                       pack_coercions := true;debug_print s;None
                   | exn -> pack_coercions := true; raise exn))
             candidates
         in
         (match selected with
         | Some x -> x
         | None -> 
              debug_print
                (lazy ("#### Coercion not packed: " ^ CicPp.ppterm t));
              t, ty, subst, metasenv, ugraph)
      | _ -> t, ty, subst, metasenv, ugraph)
    else
      t, ty, subst, metasenv, ugraph  

  and typeof_list subst metasenv context ugraph l =
    let tlbody_and_type,subst,metasenv,ugraph =
      List.fold_right
        (fun x (res,subst,metasenv,ugraph) ->
           let x',ty,subst',metasenv',ugraph1 =
             type_of_aux subst metasenv context x ugraph
           in
            (x', ty)::res,subst',metasenv',ugraph1
        ) l ([],subst,metasenv,ugraph)
    in
      tlbody_and_type,subst,metasenv,ugraph

  and eat_prods
    allow_coercions subst metasenv context he hetype args_bo_and_ty ugraph 
  =
    (* given he:hety, gives beack all (c he) such that (c e):?->? *)
    let fix_arity n metasenv context subst he hetype ugraph =
      let hetype = CicMetaSubst.apply_subst subst hetype in
      (* instead of a dummy functional type we may create the real product
       * using args_bo_and_ty, but since coercions lookup ignores the 
       * actual ariety we opt for the simple solution *)
      let fty = Cic.Prod(Cic.Anonymous, Cic.Sort Cic.Prop, Cic.Sort Cic.Prop) in
      match CoercGraph.look_for_coercion metasenv subst context hetype fty with
      | CoercGraph.NoCoercion -> []
      | CoercGraph.NotHandled ->
         raise (MoreArgsThanExpected (n,Uncertain (lazy "")))
      | CoercGraph.SomeCoercionToTgt candidates
      | CoercGraph.SomeCoercion candidates ->
          HExtlib.filter_map
            (fun (metasenv,last,coerc) -> 
              let pp t = 
                CicMetaSubst.ppterm_in_context ~metasenv subst t context in
              try
               let subst,metasenv,ugraph =
                fo_unif_subst subst context metasenv last he ugraph in
                debug_print (lazy ("New head: "^ pp coerc));
                let tty,ugraph =
                 CicTypeChecker.type_of_aux' ~subst metasenv context coerc
                  ugraph
                in 
                 debug_print (lazy (" has type: "^ pp tty));

                 Some (unvariant coerc,tty,subst,metasenv,ugraph)
              with
              | Uncertain _ | RefineFailure _
              | HExtlib.Localized (_,Uncertain _)
              | HExtlib.Localized (_,RefineFailure _) -> None 
              | exn -> assert false) 
            candidates
    in
    (* aux function to process the type of the head and the args in parallel *)
    let rec eat_prods_and_args metasenv subst context he hetype ugraph newargs =
      function
      | [] -> newargs,subst,metasenv,he,hetype,ugraph
      | (hete, hety)::tl as args ->
          match (CicReduction.whd ~subst context hetype) with 
          | Cic.Prod (n,s,t) ->
              let arg,subst,metasenv,ugraph =
                coerce_to_something allow_coercions localization_tbl 
                  hete hety s subst metasenv context ugraph in
              eat_prods_and_args 
                metasenv subst context he (CicSubstitution.subst (fst arg) t) 
                ugraph (newargs@[arg]) tl
          | _ -> 
              let he = 
                match he, newargs with
                | _, [] -> he
                | Cic.Appl l, _ -> Cic.Appl (l@List.map fst newargs)
                | _ -> Cic.Appl (he::List.map fst newargs)
              in
              (*{{{*) debug_print (lazy 
               let pp x = 
                CicMetaSubst.ppterm_in_context ~metasenv subst x context in
               "Fixing arity of: "^ pp he ^ "\n that has type: "^ pp hetype^
               "\n but is applyed to: " ^ String.concat ";" 
               (List.map (fun (t,_)->pp t) args_bo_and_ty)); (*}}}*)
              let error = ref None in
              let possible_fixes = 
               fix_arity (List.length args) metasenv context subst he hetype
                ugraph in
              match
                HExtlib.list_findopt
                 (fun (he,hetype,subst,metasenv,ugraph) _ ->
                   (* {{{ *)debug_print (lazy ("Try fix: "^
                    CicMetaSubst.ppterm_in_context ~metasenv subst he context));
                   debug_print (lazy (" of type: "^
                    CicMetaSubst.ppterm_in_context 
                    ~metasenv subst hetype context)); (* }}} *)
                   try      
                    Some (eat_prods_and_args 
                      metasenv subst context he hetype ugraph [] args)
                   with
                    | RefineFailure _ | Uncertain _
                    | HExtlib.Localized (_,RefineFailure _)
                    | HExtlib.Localized (_,Uncertain _) as exn ->
                       error := Some exn; None)
                possible_fixes
              with
              | Some x -> x
              | None ->
                 match !error with
                    None ->
                     raise 
                      (MoreArgsThanExpected
                        (List.length args, RefineFailure (lazy "")))
                  | Some exn -> raise exn
    in
    (* first we check if we are in the simple case of a meta closed term *)
    let subst,metasenv,ugraph1,hetype',he,args_bo_and_ty =
     if CicUtil.is_meta_closed (CicMetaSubst.apply_subst subst hetype) then
      (* this optimization is to postpone fix_arity (the most common case)*)
      subst,metasenv,ugraph,hetype,he,args_bo_and_ty
     else
       (* this (says CSC) is also useful to infer dependent types *)
        let pristinemenv = metasenv in
        let metasenv,hetype' = 
          mk_prod_of_metas metasenv context subst args_bo_and_ty 
        in
        try
          let subst,metasenv,ugraph = 
           fo_unif_subst_eat_prods subst context metasenv hetype hetype' ugraph
          in
          subst,metasenv,ugraph,hetype',he,args_bo_and_ty
        with RefineFailure _ | Uncertain _ ->
          subst,pristinemenv,ugraph,hetype,he,args_bo_and_ty
    in
    let coerced_args,subst,metasenv,he,t,ugraph =
     try
      eat_prods_and_args 
        metasenv subst context he hetype' ugraph1 [] args_bo_and_ty
     with
      MoreArgsThanExpected (residuals,exn) ->
        more_args_than_expected localization_tbl metasenv
         subst he context hetype' residuals args_bo_and_ty exn
    in
    he,(List.map fst coerced_args),t,subst,metasenv,ugraph

  and coerce_to_something 
    allow_coercions localization_tbl t infty expty subst metasenv context ugraph
  =
    let module CS = CicSubstitution in
    let module CR = CicReduction in
    let cs_subst = CS.subst ~avoid_beta_redexes:true in
    let coerce_atom_to_something t infty expty subst metasenv context ugraph =
      debug_print (lazy ("COERCE_ATOM_TO_SOMETHING"));
      let coer = 
        CoercGraph.look_for_coercion metasenv subst context infty expty
      in
      match coer with
      | CoercGraph.NoCoercion 
      | CoercGraph.SomeCoercionToTgt _ -> raise (RefineFailure (lazy
          "coerce_atom_to_something fails since no coercions found"))
      | CoercGraph.NotHandled when 
          not (CicUtil.is_meta_closed infty) || 
          not (CicUtil.is_meta_closed expty) -> raise (Uncertain (lazy
          "coerce_atom_to_something fails since carriers have metas"))
      | CoercGraph.NotHandled -> raise (RefineFailure (lazy
          "coerce_atom_to_something fails since no coercions found"))
      | CoercGraph.SomeCoercion candidates -> 
          debug_print (lazy (string_of_int (List.length candidates) ^ 
            " candidates found"));
          let uncertain = ref false in
          let selected = 
            let posibilities =
              HExtlib.filter_map
              (fun (metasenv,last,c) -> 
               try
                (* {{{ *) debug_print (lazy ("FO_UNIF_SUBST: " ^
                CicMetaSubst.ppterm_in_context ~metasenv subst last context ^
                " <==> " ^
                CicMetaSubst.ppterm_in_context ~metasenv subst t context ^ 
                "####" ^ CicMetaSubst.ppterm_in_context ~metasenv subst c
                context));
                debug_print (lazy ("FO_UNIF_SUBST: " ^
                CicPp.ppterm last ^ " <==> " ^ CicPp.ppterm t)); (* }}} *)
                let subst,metasenv,ugraph =
                 fo_unif_subst subst context metasenv last t ugraph
                in
                let newt,newhety,subst,metasenv,ugraph = 
                 type_of_aux subst metasenv context c ugraph in
                let newt, newty, subst, metasenv, ugraph = 
                  avoid_double_coercion context subst metasenv ugraph newt
                    expty 
                in
                let subst,metasenv,ugraph = 
                  fo_unif_subst subst context metasenv newhety expty ugraph
                in
                let b, ugraph =
                  CicReduction.are_convertible 
                    ~subst ~metasenv context infty expty ugraph
                in
                if b then 
                  Some ((t,infty), subst, metasenv, ugraph)
                else 
                 let newt =  unvariant newt in
                  Some ((newt,newty), subst, metasenv, ugraph)
               with 
               | Uncertain _ -> uncertain := true; None
               | RefineFailure _ -> None)
              candidates
            in
            match 
              List.fast_sort 
                (fun (_,_,m1,_) (_,_,m2,_) -> List.length m1 - List.length m2) 
                posibilities 
            with
            | [] -> None
            | x::_ -> Some x
          in
          match selected with
          | Some x -> x
          | None when !uncertain -> raise (Uncertain (lazy "coerce_atom fails"))
          | None -> raise (RefineFailure (lazy "coerce_atom fails"))
    in
    let rec coerce_to_something_aux 
      t infty expty subst metasenv context ugraph 
    =
      try            
        let subst, metasenv, ugraph =
          fo_unif_subst subst context metasenv infty expty ugraph
        in
        (t, expty), subst, metasenv, ugraph
      with (Uncertain _ | RefineFailure _ as exn)
        when allow_coercions && !insert_coercions ->
          let whd = CicReduction.whd ~delta:false in
          let clean t s c = whd c (CicMetaSubst.apply_subst s t) in
          let infty = clean infty subst context in
          let expty = clean expty subst context in
          let t = clean t subst context in
          (*{{{*) debug_print (lazy ("COERCE_TO_SOMETHING: " ^
          CicMetaSubst.ppterm_in_context ~metasenv subst t context ^ " : " ^
          CicMetaSubst.ppterm_in_context ~metasenv subst infty context ^" ==> "^
          CicMetaSubst.ppterm_in_context ~metasenv subst expty context));(*}}}*)
          let (coerced,_),subst,metasenv,_ as result = 
           match infty, expty, t with
           | Cic.Prod (nameprod,src,ty), Cic.Prod (_,src2,ty2),Cic.Fix (n,fl) ->
              (*{{{*) debug_print (lazy "FIX");
              (match fl with
                  [name,i,_(* infty *),bo] ->
                    let context_bo =
                     Some (Cic.Name name,Cic.Decl expty)::context in
                    let (rel1, _), subst, metasenv, ugraph =
                     coerce_to_something_aux (Cic.Rel 1) 
                       (CS.lift 1 expty) (CS.lift 1 infty) subst
                      metasenv context_bo ugraph in
                    let bo = cs_subst rel1 (CS.lift_from 2 1 bo) in
                    let (bo,_), subst, metasenv, ugraph =
                     coerce_to_something_aux bo (CS.lift 1 infty) (CS.lift 1
                     expty) subst
                      metasenv context_bo ugraph
                    in
                     (Cic.Fix (n,[name,i,expty,bo]),expty),subst,metasenv,ugraph
                | _ -> assert false (* not implemented yet *)) (*}}}*)
           | _,_, Cic.MutCase (uri,tyno,outty,m,pl) ->
               (*{{{*) debug_print (lazy "CASE");
               (* {{{ helper functions *)
               let get_cl_and_left_p uri tyno outty ugraph =
                 match CicEnvironment.get_obj ugraph uri with
                 | Cic.InductiveDefinition (tl, _, leftno, _),ugraph ->
                     let count_pis t =
                       let rec aux ctx t = 
                         match CicReduction.whd ~delta:false ctx t with
                         | Cic.Prod (name,src,tgt) ->
                             let ctx = Some (name, Cic.Decl src) :: ctx in
                             1 + aux ctx tgt
                         | _ -> 0
                       in
                         aux [] t
                     in
                     let rec skip_lambda_delifting t n =
                       match t,n with
                       | _,0 -> t
                       | Cic.Lambda (_,_,t),n -> 
                           skip_lambda_delifting
                             (CS.subst (Cic.Implicit None) t) (n - 1)
                       | _ -> assert false
                     in
                     let get_l_r_p n = function
                       | Cic.Lambda (_,Cic.MutInd _,_) -> [],[]
                       | Cic.Lambda (_,Cic.Appl (Cic.MutInd _ :: args),_) ->
                           HExtlib.split_nth n args
                       | _ -> assert false
                     in
                     let _, _, ty, cl = List.nth tl tyno in
                     let pis = count_pis ty in
                     let rno = pis - leftno in
                     let t = skip_lambda_delifting outty rno in
                     let left_p, _ = get_l_r_p leftno t in
                     let instantiale_with_left cl =
                       List.map 
                         (fun ty -> 
                           List.fold_left 
                             (fun t p -> match t with
                               | Cic.Prod (_,_,t) ->
                                   cs_subst p t
                               | _-> assert false)
                             ty left_p) 
                         cl 
                     in
                     let cl = instantiale_with_left (List.map snd cl) in
                     cl, left_p, leftno, rno, ugraph
                 | _ -> raise exn
               in
               let rec keep_lambdas_and_put_expty ctx t bo right_p matched n =
                 match t,n with
                 | _,0 ->
                   let rec mkr n = function 
                     | [] -> [] | _::tl -> Cic.Rel n :: mkr (n+1) tl
                   in
                   let bo =
                   CicReplace.replace_lifting
                     ~equality:(fun _ -> CicUtil.alpha_equivalence)
                     ~context:ctx
                     ~what:(matched::right_p)
                     ~with_what:(Cic.Rel 1::List.rev (mkr 2 right_p))
                     ~where:bo
                   in
                   bo
                 | Cic.Lambda (name, src, tgt),_ ->
                     Cic.Lambda (name, src,
                      keep_lambdas_and_put_expty 
                       (Some (name, Cic.Decl src)::ctx) tgt (CS.lift 1 bo)
                       (List.map (CS.lift 1) right_p) (CS.lift 1 matched) (n-1))
                 | _ -> assert false
               in
               let eq_uri, eq, eq_refl = 
                 match LibraryObjects.eq_URI () with 
                 | None -> HLog.warn "no default equality"; raise exn
                 | Some u -> u, Cic.MutInd(u,0,[]), Cic.MutConstruct (u,0,1,[])
               in
               let add_params 
                 metasenv subst context uri tyno cty outty mty m leftno i 
               =
                 let rec aux context outty par k mty m = function
                   | Cic.Prod (name, src, tgt) ->
                       let t,k = 
                         aux 
                           (Some (name, Cic.Decl src) :: context)
                           (CS.lift 1 outty) (Cic.Rel k::par) (k+1) 
                           (CS.lift 1 mty) (CS.lift 1 m) tgt
                       in
                       Cic.Prod (name, src, t), k
                   | Cic.MutInd _ ->
                       let k = 
                         let k = Cic.MutConstruct (uri,tyno,i,[]) in
                         if par <> [] then Cic.Appl (k::par) else k
                       in
                       Cic.Prod (Cic.Name "p", 
                        Cic.Appl [eq; mty; m; k],
                        (CS.lift 1
                         (CR.head_beta_reduce ~delta:false 
                          (Cic.Appl [outty;k])))),k
                   | Cic.Appl (Cic.MutInd _::pl) ->
                       let left_p,right_p = HExtlib.split_nth leftno pl in
                       let has_rights = right_p <> [] in
                       let k = 
                         let k = Cic.MutConstruct (uri,tyno,i,[]) in
                         Cic.Appl (k::left_p@par)
                       in
                       let right_p = 
                         try match 
                           CicTypeChecker.type_of_aux' ~subst metasenv context k
                             CicUniv.oblivion_ugraph 
                         with
                         | Cic.Appl (Cic.MutInd _::args),_ ->
                             snd (HExtlib.split_nth leftno args)
                         | _ -> assert false
                         with CicTypeChecker.TypeCheckerFailure _-> assert false
                       in
                       if has_rights then
                         CR.head_beta_reduce ~delta:false 
                           (Cic.Appl (outty ::right_p @ [k])),k
                       else
                         Cic.Prod (Cic.Name "p", 
                          Cic.Appl [eq; mty; m; k],
                          (CS.lift 1
                           (CR.head_beta_reduce ~delta:false 
                            (Cic.Appl (outty ::right_p @ [k]))))),k
                   | _ -> assert false
                 in
                   aux context outty [] 1 mty m cty
               in
               let add_lambda_for_refl_m pbo rno mty m k cty =
                 (* k lives in the right context *)
                 if rno <> 0 then pbo else
                 let rec aux mty m = function 
                   | Cic.Lambda (name,src,bo), Cic.Prod (_,_,ty) ->
                      Cic.Lambda (name,src,
                       (aux (CS.lift 1 mty) (CS.lift 1 m) (bo,ty)))
                   | t,_ -> 
                       Cic.Lambda (Cic.Name "p",
                         Cic.Appl [eq; mty; m; k],CS.lift 1 t)
                 in
                 aux mty m (pbo,cty)
               in
               let add_pi_for_refl_m new_outty mty m rno =
                 if rno <> 0 then new_outty else
                   let rec aux m mty = function
                     | Cic.Lambda (name, src, tgt) ->
                         Cic.Lambda (name, src, 
                           aux (CS.lift 1 m) (CS.lift 1 mty) tgt)
                     | t ->
                         Cic.Prod 
                           (Cic.Anonymous, Cic.Appl [eq;mty;m;Cic.Rel 1],
                           CS.lift 1 t)
                   in
                     aux m mty new_outty
               in (* }}} end helper functions *)
               (* constructors types with left params already instantiated *)
               let outty = CicMetaSubst.apply_subst subst outty in
               let cl, left_p, leftno,rno,ugraph = 
                 get_cl_and_left_p uri tyno outty ugraph 
               in
               let right_p, mty = 
                 try
                   match 
                     CicTypeChecker.type_of_aux' ~subst metasenv context m
                       CicUniv.oblivion_ugraph 
                   with
                   | (Cic.MutInd _ | Cic.Meta _) as mty,_ -> [], mty
                   | Cic.Appl ((Cic.MutInd _|Cic.Meta _)::args) as mty,_ ->
                       snd (HExtlib.split_nth leftno args), mty
                   | _ -> assert false
                 with CicTypeChecker.TypeCheckerFailure _ -> 
                    raise (AssertFailure(lazy "already ill-typed matched term"))
               in
               let new_outty =
                keep_lambdas_and_put_expty context outty expty right_p m (rno+1)
               in
               debug_print 
                 (lazy ("CASE: new_outty: " ^ CicMetaSubst.ppterm_in_context 
                  ~metasenv subst new_outty context));
               let _,pl,subst,metasenv,ugraph = 
                 List.fold_right2
                   (fun cty pbo (i, acc, s, menv, ugraph) -> 
                     (* Pi k_par, (Pi H:m=(K_i left_par k_par)), 
                      *   (new_)outty right_par (K_i left_par k_par) *)
                      let infty_pbo, _ = 
                        add_params menv s context uri tyno 
                          cty outty mty m leftno i in
                      debug_print 
                       (lazy ("CASE: infty_pbo: "^CicMetaSubst.ppterm_in_context
                        ~metasenv subst infty_pbo context));
                      let expty_pbo, k = (* k is (K_i left_par k_par) *)
                        add_params menv s context uri tyno 
                          cty new_outty mty m leftno i in
                      debug_print 
                       (lazy ("CASE: expty_pbo: "^CicMetaSubst.ppterm_in_context
                        ~metasenv subst expty_pbo context));
                      let pbo = add_lambda_for_refl_m pbo rno mty m k cty in
                      debug_print 
                        (lazy ("CASE: pbo: " ^ CicMetaSubst.ppterm_in_context 
                        ~metasenv subst pbo context));
                      let (pbo, _), subst, metasenv, ugraph =
                        coerce_to_something_aux pbo infty_pbo expty_pbo 
                          s menv context ugraph
                      in
                      debug_print 
                        (lazy ("CASE: pbo: " ^ CicMetaSubst.ppterm_in_context 
                        ~metasenv subst pbo context));
                      (i-1, pbo::acc, subst, metasenv, ugraph))
                   cl pl (List.length pl, [], subst, metasenv, ugraph)
               in
               let new_outty = add_pi_for_refl_m new_outty mty m rno in
               debug_print 
                 (lazy ("CASE: new_outty: " ^ CicMetaSubst.ppterm_in_context 
                  ~metasenv subst new_outty context));
               let t = 
                 if rno = 0 then
                   let refl_m=Cic.Appl[eq_refl;mty;m]in
                   Cic.Appl [Cic.MutCase(uri,tyno,new_outty,m,pl);refl_m] 
                 else 
                   Cic.MutCase(uri,tyno,new_outty,m,pl)
               in
               (t, expty), subst, metasenv, ugraph (*}}}*)
           | Cic.Prod (nameprod, src, ty),Cic.Prod (_, src2, ty2), _ -> 
               (*{{{*) debug_print (lazy "LAM");
               let name_con = 
                 FreshNamesGenerator.mk_fresh_name 
                   ~subst metasenv context ~typ:src2 Cic.Anonymous
               in
               let context_src2 = (Some (name_con, Cic.Decl src2) :: context) in
               (* contravariant part: the argument of f:src->ty *)
               let (rel1, _), subst, metasenv, ugraph = 
                 coerce_to_something_aux
                  (Cic.Rel 1) (CS.lift 1 src2) 
                  (CS.lift 1 src) subst metasenv context_src2 ugraph
               in
               (* covariant part: the result of f(c x); x:src2; (c x):src *)
               let name_t, bo = 
                 match t with
                 | Cic.Lambda (n,_,bo) -> n, cs_subst rel1 (CS.lift_from 2 1 bo)
                 | _ -> name_con, Cic.Appl[CS.lift 1 t;rel1]
               in
               (* we fix the possible dependency problem in the source ty *)
               let ty = cs_subst rel1 (CS.lift_from 2 1 ty) in
               let (bo, _), subst, metasenv, ugraph = 
                 coerce_to_something_aux
                   bo ty ty2 subst metasenv context_src2 ugraph
               in
               let coerced = Cic.Lambda (name_t,src2, bo) in
               (coerced, expty), subst, metasenv, ugraph (*}}}*)
           | _ -> 
               (*{{{*)debug_print (lazy ("ATOM: "^CicMetaSubst.ppterm_in_context
                ~metasenv subst infty context ^ " ==> " ^
                CicMetaSubst.ppterm_in_context ~metasenv subst expty context));
               coerce_atom_to_something
               t infty expty subst metasenv context ugraph (*}}}*)
          in
          debug_print (lazy ("COERCE TO SOMETHING END: "^
            CicMetaSubst.ppterm_in_context ~metasenv subst coerced context));
          result
    in
    try
      coerce_to_something_aux t infty expty subst metasenv context ugraph
    with Uncertain _ | RefineFailure _ as exn ->
      let f _ =
        lazy ("(9) The term " ^
          CicMetaSubst.ppterm_in_context metasenv subst t context ^ 
          " has type " ^ CicMetaSubst.ppterm_in_context metasenv subst
          infty context ^ " but is here used with type " ^ 
          CicMetaSubst.ppterm_in_context metasenv subst expty context)
      in
        enrich localization_tbl ~f t exn

  and coerce_to_sort localization_tbl t infty subst context metasenv uragph =
    match CicReduction.whd ~delta:false ~subst context infty with
    | Cic.Meta _ | Cic.Sort _ -> 
        t,infty, subst, metasenv, ugraph
    | src ->
       debug_print (lazy ("COERCE TO SORT: "^CicMetaSubst.ppterm_in_context
         ~metasenv subst src context));
       let tgt = Cic.Sort (Cic.Type (CicUniv.fresh())) in
       try
         let (t, ty_t), subst, metasenv, ugraph =
           coerce_to_something true
             localization_tbl t src tgt subst metasenv context ugraph
         in
         debug_print (lazy ("COERCE TO SORT END: "^ 
           CicMetaSubst.ppterm_in_context ~metasenv subst t context));
         t, ty_t, subst, metasenv, ugraph
       with HExtlib.Localized (_, exn) -> 
         let f _ = 
           lazy ("(7)The term " ^ 
            CicMetaSubst.ppterm_in_context ~metasenv subst t context 
            ^ " is not a type since it has type " ^ 
            CicMetaSubst.ppterm_in_context ~metasenv subst src context
            ^ " that is not a sort")
         in
           enrich localization_tbl ~f t exn
  in
  
  (* eat prods ends here! *)
  
  let t',ty,subst',metasenv',ugraph1 =
   type_of_aux subst metasenv context t ugraph
  in
  let substituted_t = CicMetaSubst.apply_subst subst' t' in
  let substituted_ty = CicMetaSubst.apply_subst subst' ty in
    (* Andrea: ho rimesso qui l'applicazione della subst al
       metasenv dopo che ho droppato l'invariante che il metsaenv
       e' sempre istanziato *)
  let substituted_metasenv = 
    CicMetaSubst.apply_subst_metasenv subst' metasenv' in
    (* metasenv' *)
    (*  substituted_t,substituted_ty,substituted_metasenv *)
    (* ANDREA: spostare tutta questa robaccia da un altra parte *)
  let cleaned_t =
   if clean_dummy_dependent_types then
    FreshNamesGenerator.clean_dummy_dependent_types substituted_t
   else substituted_t in
  let cleaned_ty =
   if clean_dummy_dependent_types then
    FreshNamesGenerator.clean_dummy_dependent_types substituted_ty
   else substituted_ty in
  let cleaned_metasenv =
   if clean_dummy_dependent_types then
    List.map
      (function (n,context,ty) ->
         let ty' = FreshNamesGenerator.clean_dummy_dependent_types ty in
         let context' =
           List.map
             (function
                  None -> None
                | Some (n, Cic.Decl t) ->
                    Some (n,
                          Cic.Decl (FreshNamesGenerator.clean_dummy_dependent_types t))
                | Some (n, Cic.Def (bo,ty)) ->
                    let bo' = FreshNamesGenerator.clean_dummy_dependent_types bo in
                    let ty' = FreshNamesGenerator.clean_dummy_dependent_types ty
                    in
                      Some (n, Cic.Def (bo',ty'))
             ) context
         in
           (n,context',ty')
      ) substituted_metasenv
   else
    substituted_metasenv
  in
    (cleaned_t,cleaned_ty,cleaned_metasenv,subst',ugraph1) 
;;

let type_of metasenv subst context t ug =
  type_of_aux' metasenv subst context t ug
;;

let type_of_aux' 
  ?clean_dummy_dependent_types ?localization_tbl metasenv context t ug
=
  let t,ty,m,s,ug = 
    type_of_aux' ?clean_dummy_dependent_types ?localization_tbl 
      metasenv [] context t ug
  in
  t,ty,m,ug
;;

let undebrujin uri typesno tys t =
  snd
   (List.fold_right
     (fun (name,_,_,_) (i,t) ->
       (* here the explicit_named_substituion is assumed to be *)
       (* of length 0 *)
       let t' = Cic.MutInd (uri,i,[])  in
       let t = CicSubstitution.subst t' t in
        i - 1,t
     ) tys (typesno - 1,t)) 

let map_first_n n start f g l = 
  let rec aux acc k l =
    if k < n then
      match l with
      | [] -> raise (Invalid_argument "map_first_n")
      | hd :: tl -> f hd k (aux acc (k+1) tl)
    else
      g acc l
  in
  aux start 0 l
   
(*CSC: this is a very rough approximation; to be finished *)
let are_all_occurrences_positive metasenv ugraph uri tys leftno =
  let subst,metasenv,ugraph,tys = 
    List.fold_right
      (fun (name,ind,arity,cl) (subst,metasenv,ugraph,acc) ->
        let subst,metasenv,ugraph,cl = 
          List.fold_right
            (fun (name,ty) (subst,metasenv,ugraph,acc) ->
               let rec aux ctx k subst = function
                 | Cic.Appl((Cic.MutInd (uri',_,_)as hd)::tl) when uri = uri'->
                     let subst,metasenv,ugraph,tl = 
                       map_first_n leftno 
                         (subst,metasenv,ugraph,[]) 
                         (fun t n (subst,metasenv,ugraph,acc) ->
                           let subst,metasenv,ugraph = 
                             fo_unif_subst 
                               subst ctx metasenv t (Cic.Rel (k-n)) ugraph 
                           in
                           subst,metasenv,ugraph,(t::acc)) 
                         (fun (s,m,g,acc) tl -> assert(acc=[]);(s,m,g,tl)) 
                         tl
                     in
                     subst,metasenv,ugraph,(Cic.Appl (hd::tl))
                 | Cic.MutInd(uri',_,_) as t when uri = uri'->
                     subst,metasenv,ugraph,t 
                 | Cic.Prod (name,s,t) -> 
                     let ctx = (Some (name,Cic.Decl s))::ctx in 
                     let subst,metasenv,ugraph,t = aux ctx (k+1) subst t in
                     subst,metasenv,ugraph,Cic.Prod (name,s,t)
                 | _ -> 
                     raise 
                      (RefineFailure 
                        (lazy "not well formed constructor type"))
               in
               let subst,metasenv,ugraph,ty = aux [] 0 subst ty in  
               subst,metasenv,ugraph,(name,ty) :: acc)
          cl (subst,metasenv,ugraph,[])
        in 
        subst,metasenv,ugraph,(name,ind,arity,cl)::acc)
      tys ([],metasenv,ugraph,[])
  in
  let substituted_tys = 
    List.map 
      (fun (name,ind,arity,cl) -> 
        let cl = 
          List.map (fun (name, ty) -> name,CicMetaSubst.apply_subst subst ty) cl
        in
        name,ind,CicMetaSubst.apply_subst subst arity,cl)
      tys 
  in
  metasenv,ugraph,substituted_tys
    
let typecheck metasenv uri obj ~localization_tbl =
 let ugraph = CicUniv.oblivion_ugraph in
 match obj with
    Cic.Constant (name,Some bo,ty,args,attrs) ->
     (* CSC: ugly code. Here I need to retrieve in advance the loc of bo
        since type_of_aux' destroys localization information (which are
        preserved by type_of_aux *)
     let loc exn' =
      try
       Cic.CicHash.find localization_tbl bo
      with Not_found ->
       HLog.debug ("!!! NOT LOCALIZED: " ^ CicPp.ppterm bo);
       raise exn' in
     let bo',boty,metasenv,ugraph =
      type_of_aux' ~localization_tbl metasenv [] bo ugraph in
     let ty',_,metasenv,ugraph =
      type_of_aux' ~localization_tbl metasenv [] ty ugraph in
     let subst,metasenv,ugraph =
      try
       fo_unif_subst [] [] metasenv boty ty' ugraph
      with
         RefineFailure _
       | Uncertain _ as exn ->
          let msg = 
            lazy ("(1) The term " ^
             CicMetaSubst.ppterm_in_context ~metasenv [] bo' [] ^
             " has type " ^
             CicMetaSubst.ppterm_in_context ~metasenv [] boty [] ^
             " but is here used with type " ^
             CicMetaSubst.ppterm_in_context ~metasenv [] ty' [])
          in
           let exn' =
            match exn with
               RefineFailure _ -> RefineFailure msg
             | Uncertain _ -> Uncertain msg
             | _ -> assert false
           in
            raise (HExtlib.Localized (loc exn',exn'))
     in
     let bo' = CicMetaSubst.apply_subst subst bo' in
     let ty' = CicMetaSubst.apply_subst subst ty' in
     let metasenv = CicMetaSubst.apply_subst_metasenv subst metasenv in
      Cic.Constant (name,Some bo',ty',args,attrs),metasenv,ugraph
  | Cic.Constant (name,None,ty,args,attrs) ->
     let ty',sort,metasenv,ugraph =
      type_of_aux' ~localization_tbl metasenv [] ty ugraph
     in
      (match CicReduction.whd [] sort with
          Cic.Sort _
        | Cic.Meta _ -> Cic.Constant (name,None,ty',args,attrs),metasenv,ugraph
        | _ -> raise (RefineFailure (lazy "")))
  | Cic.CurrentProof (name,metasenv',bo,ty,args,attrs) ->
     assert (metasenv' = metasenv);
     (* Here we do not check the metasenv for correctness *)
     let bo',boty,metasenv,ugraph =
      type_of_aux' ~localization_tbl metasenv [] bo ugraph in
     let ty',sort,metasenv,ugraph =
      type_of_aux' ~localization_tbl metasenv [] ty ugraph in
     begin
       match CicReduction.whd ~delta:true [] sort with
         Cic.Sort _
       (* instead of raising Uncertain, let's hope that the meta will become
          a sort *)
       | Cic.Meta _ -> ()
       | _ -> raise (RefineFailure (lazy "The term provided is not a type"))
     end;
     let subst,metasenv,ugraph = fo_unif_subst [] [] metasenv boty ty' ugraph in
     let bo' = CicMetaSubst.apply_subst subst bo' in
     let ty' = CicMetaSubst.apply_subst subst ty' in
     let metasenv = CicMetaSubst.apply_subst_metasenv subst metasenv in
      Cic.CurrentProof (name,metasenv,bo',ty',args,attrs),metasenv,ugraph
  | Cic.Variable _ -> assert false (* not implemented *)
  | Cic.InductiveDefinition (tys,args,paramsno,attrs) ->
     (*CSC: this code is greately simplified and many many checks are missing *)
     (*CSC: e.g. the constructors are not required to build their own types,  *)
     (*CSC: the arities are not required to have as type a sort, etc.         *)
     let uri = match uri with Some uri -> uri | None -> assert false in
     let typesno = List.length tys in
     (* first phase: we fix only the types *)
     let metasenv,ugraph,tys =
      List.fold_right
       (fun (name,b,ty,cl) (metasenv,ugraph,res) ->
         let ty',_,metasenv,ugraph =
          (* clean_dummy_dependent_types: false to avoid cleaning the names
             of the left products, that must be identical to those of the
             constructors; however, non-left products should probably be
             cleaned *)
          type_of_aux' ~clean_dummy_dependent_types:false ~localization_tbl
           metasenv [] ty ugraph
         in
          metasenv,ugraph,(name,b,ty',cl)::res
       ) tys (metasenv,ugraph,[]) in
     let con_context =
      List.rev_map (fun (name,_,ty,_)-> Some (Cic.Name name,Cic.Decl ty)) tys in
     (* second phase: we fix only the constructors *)
     let saved_menv = metasenv in
     let metasenv,ugraph,tys =
      List.fold_right
       (fun (name,b,ty,cl) (metasenv,ugraph,res) ->
         let metasenv,ugraph,cl' =
          List.fold_right
           (fun (name,ty) (metasenv,ugraph,res) ->
             let ty =
              CicTypeChecker.debrujin_constructor
              ~cb:(relocalize localization_tbl) uri typesno [] ty in
             let ty',_,metasenv,ugraph =
              type_of_aux' ~localization_tbl metasenv con_context ty ugraph in
             let ty' = undebrujin uri typesno tys ty' in
              metasenv@saved_menv,ugraph,(name,ty')::res
           ) cl (metasenv,ugraph,[])
         in
          metasenv,ugraph,(name,b,ty,cl')::res
       ) tys (metasenv,ugraph,[]) in
     (* third phase: we check the positivity condition *)
     let metasenv,ugraph,tys = 
       are_all_occurrences_positive metasenv ugraph uri tys paramsno 
     in
     Cic.InductiveDefinition (tys,args,paramsno,attrs),metasenv,ugraph
;;

(* sara' piu' veloce che raffinare da zero? mah.... *)
let pack_coercion metasenv ctx t =
 let module C = Cic in
 let rec merge_coercions ctx =
   let aux = (fun (u,t) -> u,merge_coercions ctx t) in
   function
   | C.Rel _ | C.Sort _ | C.Implicit _ as t -> t
   | C.Meta (n,subst) ->
      let subst' =
       List.map
        (function None -> None | Some t -> Some (merge_coercions ctx t)) subst
      in
       C.Meta (n,subst')
   | C.Cast (te,ty) -> C.Cast (merge_coercions ctx te, merge_coercions ctx ty)
   | C.Prod (name,so,dest) -> 
       let ctx' = (Some (name,C.Decl so))::ctx in
       C.Prod (name, merge_coercions ctx so, merge_coercions ctx' dest) 
   | C.Lambda (name,so,dest) -> 
       let ctx' = (Some (name,C.Decl so))::ctx in
       C.Lambda (name, merge_coercions ctx so, merge_coercions ctx' dest)
   | C.LetIn (name,so,ty,dest) -> 
       let ctx' = Some (name,(C.Def (so,ty)))::ctx in
       C.LetIn
        (name, merge_coercions ctx so, merge_coercions ctx ty,
         merge_coercions ctx' dest)
   | C.Appl l -> 
      let l = List.map (merge_coercions ctx) l in
      let t = C.Appl l in
       let b,_,_,_,_ = is_a_double_coercion t in
       if b then
         let ugraph = CicUniv.oblivion_ugraph in
         let old_insert_coercions = !insert_coercions in
         insert_coercions := false;
         let newt, _, menv, _ = 
           try 
             type_of_aux' metasenv ctx t ugraph 
           with RefineFailure _ | Uncertain _ -> 
             t, t, [], ugraph 
         in
         insert_coercions := old_insert_coercions;
         if metasenv <> [] || menv = [] then 
           newt 
         else 
           (prerr_endline "PUO' SUCCEDERE!!!!!";t)
       else
         t
   | C.Var (uri,exp_named_subst) -> 
       let exp_named_subst = List.map aux exp_named_subst in
       C.Var (uri, exp_named_subst)
   | C.Const (uri,exp_named_subst) ->
       let exp_named_subst = List.map aux exp_named_subst in
       C.Const (uri, exp_named_subst)
   | C.MutInd (uri,tyno,exp_named_subst) ->
       let exp_named_subst = List.map aux exp_named_subst in
       C.MutInd (uri,tyno,exp_named_subst)
   | C.MutConstruct (uri,tyno,consno,exp_named_subst) ->
       let exp_named_subst = List.map aux exp_named_subst in
       C.MutConstruct (uri,tyno,consno,exp_named_subst)  
   | C.MutCase (uri,tyno,out,te,pl) ->
       let pl = List.map (merge_coercions ctx) pl in
       C.MutCase (uri,tyno,merge_coercions ctx out, merge_coercions ctx te, pl)
   | C.Fix (fno, fl) ->
       let ctx' =
         List.fold_left
           (fun l (n,_,ty,_) -> (Some (C.Name n,C.Decl ty))::l) 
           ctx fl
       in 
       let fl = 
         List.map 
           (fun (name,idx,ty,bo) -> 
             (name,idx,merge_coercions ctx ty,merge_coercions ctx' bo)) 
         fl
       in
       C.Fix (fno, fl)
   | C.CoFix (fno, fl) ->
       let ctx' =
         List.fold_left
           (fun l (n,ty,_) -> (Some (C.Name n,C.Decl ty))::l) 
           ctx fl
       in 
       let fl = 
         List.map 
           (fun (name,ty,bo) -> 
             (name, merge_coercions ctx ty, merge_coercions ctx' bo)) 
         fl 
       in
       C.CoFix (fno, fl)
 in
  merge_coercions ctx t
;;

let pack_coercion_metasenv conjectures = conjectures (*

  TASSI: this code war written when coercions were a toy,
         now packing coercions involves unification thus
         the metasenv may change, and this pack coercion 
         does not handle that.

  let module C = Cic in
  List.map 
    (fun (i, ctx, ty) -> 
       let ctx = 
         List.fold_right 
           (fun item ctx ->
              let item' =
                match item with
                    Some (name, C.Decl t) -> 
                      Some (name, C.Decl (pack_coercion conjectures ctx t))
                  | Some (name, C.Def (t,None)) -> 
                      Some (name,C.Def (pack_coercion conjectures ctx t,None))
                  | Some (name, C.Def (t,Some ty)) -> 
                      Some (name, C.Def (pack_coercion conjectures ctx t, 
					 Some (pack_coercion conjectures ctx ty)))
                  | None -> None
              in
                item'::ctx
           ) ctx []
       in
         ((i,ctx,pack_coercion conjectures ctx ty))
    ) conjectures
    *)
;;

let pack_coercion_obj obj = obj (*

  TASSI: this code war written when coercions were a toy,
         now packing coercions involves unification thus
         the metasenv may change, and this pack coercion 
         does not handle that.

  let module C = Cic in
  match obj with
  | C.Constant (id, body, ty, params, attrs) -> 
      let body = 
        match body with 
        | None -> None 
        | Some body -> Some (pack_coercion [] [] body) 
      in
      let ty = pack_coercion [] [] ty in
        C.Constant (id, body, ty, params, attrs)
  | C.Variable (name, body, ty, params, attrs) ->
      let body = 
        match body with 
        | None -> None 
        | Some body -> Some (pack_coercion [] [] body) 
      in
      let ty = pack_coercion [] [] ty in
        C.Variable (name, body, ty, params, attrs)
  | C.CurrentProof (name, conjectures, body, ty, params, attrs) ->
      let conjectures = pack_coercion_metasenv conjectures in
      let body = pack_coercion conjectures [] body in
      let ty = pack_coercion conjectures [] ty in
      C.CurrentProof (name, conjectures, body, ty, params, attrs)
  | C.InductiveDefinition (indtys, params, leftno, attrs) ->
      let indtys = 
        List.map 
          (fun (name, ind, arity, cl) -> 
            let arity = pack_coercion [] [] arity in
            let cl = 
              List.map (fun (name, ty) -> (name,pack_coercion [] [] ty)) cl 
            in
            (name, ind, arity, cl))
          indtys
      in
        C.InductiveDefinition (indtys, params, leftno, attrs) *)
;;


(* DEBUGGING ONLY 
let type_of_aux' metasenv context term =
 try
  let (t,ty,m) = 
      type_of_aux' metasenv context term in
    debug_print (lazy
     ("@@@ REFINE SUCCESSFUL: " ^ CicPp.ppterm t ^ " : " ^ CicPp.ppterm ty));
   debug_print (lazy
    ("@@@ REFINE SUCCESSFUL (metasenv):\n" ^ CicMetaSubst.ppmetasenv ~sep:";" m []));
   (t,ty,m)
 with
 | RefineFailure msg as e ->
     debug_print (lazy ("@@@ REFINE FAILED: " ^ msg));
     raise e
 | Uncertain msg as e ->
     debug_print (lazy ("@@@ REFINE UNCERTAIN: " ^ msg));
     raise e
;; *)

let profiler2 = HExtlib.profile "CicRefine"

let type_of_aux' ?localization_tbl metasenv context term ugraph =
 profiler2.HExtlib.profile
  (type_of_aux' ?localization_tbl metasenv context term) ugraph

let typecheck ~localization_tbl metasenv uri obj =
 profiler2.HExtlib.profile (typecheck ~localization_tbl metasenv uri) obj

let _ = DoubleTypeInference.pack_coercion := pack_coercion;;
(* vim:set foldmethod=marker: *)
