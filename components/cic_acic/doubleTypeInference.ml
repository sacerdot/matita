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

exception Impossible of int;;
exception NotWellTyped of string;;
exception WrongUriToConstant of string;;
exception WrongUriToVariable of string;;
exception WrongUriToMutualInductiveDefinitions of string;;
exception ListTooShort;;
exception RelToHiddenHypothesis;;

(*CSC: must alfa-conversion be considered or not? *)

let xxx_type_of_aux' m c t =
 try 
   Some (fst (CicTypeChecker.type_of_aux' m c t CicUniv.oblivion_ugraph))
 with
 | CicTypeChecker.TypeCheckerFailure _ -> None (* because eta_expansion *)
;;

type types = {synthesized : Cic.term ; expected : Cic.term option};;

(* does_not_occur n te                              *)
(* returns [true] if [Rel n] does not occur in [te] *)
let rec does_not_occur n =
 let module C = Cic in
  function
     C.Rel m when m = n -> false
   | C.Rel _
(* FG/CSC: maybe we assume the meta is guarded so we do not recur on its *)
(*         explicit subsitutions (copied from the kernel) ???            *)
   | C.Meta _
   | C.Sort _
   | C.Implicit _ -> true 
   | C.Cast (te,ty) ->
      does_not_occur n te && does_not_occur n ty
   | C.Prod (name,so,dest) ->
      does_not_occur n so &&
       does_not_occur (n + 1) dest
   | C.Lambda (name,so,dest) ->
      does_not_occur n so &&
       does_not_occur (n + 1) dest
   | C.LetIn (name,so,ty,dest) ->
      does_not_occur n so &&
       does_not_occur n ty &&
        does_not_occur (n + 1) dest
   | C.Appl l ->
      List.fold_right (fun x i -> i && does_not_occur n x) l true
   | C.Var (_,exp_named_subst)
   | C.Const (_,exp_named_subst)
   | C.MutInd (_,_,exp_named_subst)
   | C.MutConstruct (_,_,_,exp_named_subst) ->
      List.fold_right (fun (_,x) i -> i && does_not_occur n x)
       exp_named_subst true
   | C.MutCase (_,_,out,te,pl) ->
      does_not_occur n out && does_not_occur n te &&
       List.fold_right (fun x i -> i && does_not_occur n x) pl true
   | C.Fix (_,fl) ->
      let len = List.length fl in
       let n_plus_len = n + len in
        List.fold_right
         (fun (_,_,ty,bo) i ->
           i && does_not_occur n ty &&
           does_not_occur n_plus_len bo
         ) fl true
   | C.CoFix (_,fl) ->
      let len = List.length fl in
       let n_plus_len = n + len in
        List.fold_right
         (fun (_,ty,bo) i ->
           i && does_not_occur n ty &&
           does_not_occur n_plus_len bo
         ) fl true
;;

(* FG: if ~clean:true, unreferenced letins are removed *)
(*     (beta-reducttion can cause unreferenced letins) *)
let rec beta_reduce ?(clean=false)=
 let module S = CicSubstitution in
 let module C = Cic in
  function
      C.Rel _ as t -> t
    | C.Var (uri,exp_named_subst) ->
       let exp_named_subst' =
        List.map (function (i,t) -> i, beta_reduce ~clean t) exp_named_subst
       in
        C.Var (uri,exp_named_subst')
    | C.Meta (n,l) ->
       C.Meta (n,
        List.map
         (function None -> None | Some t -> Some (beta_reduce ~clean t)) l
       )
    | C.Sort _ as t -> t
    | C.Implicit _ -> assert false
    | C.Cast (te,ty) ->
       C.Cast (beta_reduce ~clean te, beta_reduce ~clean ty)
    | C.Prod (n,s,t) ->
       C.Prod (n, beta_reduce ~clean s, beta_reduce ~clean t)
    | C.Lambda (n,s,t) ->
       C.Lambda (n, beta_reduce ~clean s, beta_reduce ~clean t)
    | C.LetIn (n,s,ty,t) ->
       let t' = beta_reduce ~clean t in
       if clean && does_not_occur 1 t' then
	  (* since [Rel 1] does not occur in typ, substituting any term *)
          (* in place of [Rel 1] is equivalent to delifting once        *)
          CicSubstitution.subst (C.Implicit None) t'
       else
          C.LetIn (n, beta_reduce ~clean s, beta_reduce ~clean ty, t')
    | C.Appl ((C.Lambda (name,s,t))::he::tl) ->
       let he' = S.subst he t in
        if tl = [] then
         beta_reduce ~clean he'
        else
         (match he' with
             C.Appl l -> beta_reduce ~clean (C.Appl (l@tl))
           | _ -> beta_reduce ~clean (C.Appl (he'::tl)))
    | C.Appl l ->
       C.Appl (List.map (beta_reduce ~clean) l)
    | C.Const (uri,exp_named_subst) ->
       let exp_named_subst' =
        List.map (function (i,t) -> i, beta_reduce ~clean t) exp_named_subst
       in
        C.Const (uri,exp_named_subst')
    | C.MutInd (uri,i,exp_named_subst) ->
       let exp_named_subst' =
        List.map (function (i,t) -> i, beta_reduce ~clean t) exp_named_subst
       in
        C.MutInd (uri,i,exp_named_subst')
    | C.MutConstruct (uri,i,j,exp_named_subst) ->
       let exp_named_subst' =
        List.map (function (i,t) -> i, beta_reduce ~clean t) exp_named_subst
       in
        C.MutConstruct (uri,i,j,exp_named_subst')
    | C.MutCase (sp,i,outt,t,pl) ->
       C.MutCase (sp,i,beta_reduce ~clean outt,beta_reduce ~clean t,
        List.map (beta_reduce ~clean) pl)
    | C.Fix (i,fl) ->
       let fl' =
        List.map
         (function (name,i,ty,bo) ->
           name,i,beta_reduce ~clean ty,beta_reduce ~clean bo
         ) fl
       in
        C.Fix (i,fl')
    | C.CoFix (i,fl) ->
       let fl' =
        List.map
         (function (name,ty,bo) ->
           name,beta_reduce ~clean ty,beta_reduce ~clean bo
         ) fl
       in
        C.CoFix (i,fl')
;;

let rec split l n =
 match (l,n) with
    (l,0) -> ([], l)
  | (he::tl, n) -> let (l1,l2) = split tl (n-1) in (he::l1,l2)
  | (_,_) -> raise ListTooShort
;;

let type_of_constant uri =
 let module C = Cic in
 let module R = CicReduction in
 let module U = UriManager in
  let cobj =
   match CicEnvironment.is_type_checked CicUniv.oblivion_ugraph uri with
      CicEnvironment.CheckedObj (cobj,_) -> cobj
    | CicEnvironment.UncheckedObj (uobj,_) ->
       raise (NotWellTyped "Reference to an unchecked constant")
  in
   match cobj with
      C.Constant (_,_,ty,_,_) -> ty
    | C.CurrentProof (_,_,_,ty,_,_) -> ty
    | _ -> raise (WrongUriToConstant (U.string_of_uri uri))
;;

let type_of_variable uri =
 let module C = Cic in
 let module R = CicReduction in
 let module U = UriManager in
  match CicEnvironment.is_type_checked CicUniv.oblivion_ugraph uri with
     CicEnvironment.CheckedObj ((C.Variable (_,_,ty,_,_)),_) -> ty
   | CicEnvironment.UncheckedObj (C.Variable _,_) ->
      raise (NotWellTyped "Reference to an unchecked variable")
   |  _ -> raise (WrongUriToVariable (UriManager.string_of_uri uri))
;;

let type_of_mutual_inductive_defs uri i =
 let module C = Cic in
 let module R = CicReduction in
 let module U = UriManager in
  let cobj =
   match CicEnvironment.is_type_checked CicUniv.oblivion_ugraph uri with
      CicEnvironment.CheckedObj (cobj,_) -> cobj
    | CicEnvironment.UncheckedObj (uobj,_) ->
       raise (NotWellTyped "Reference to an unchecked inductive type")
  in
   match cobj with
      C.InductiveDefinition (dl,_,_,_) ->
       let (_,_,arity,_) = List.nth dl i in
        arity
    | _ -> raise (WrongUriToMutualInductiveDefinitions (U.string_of_uri uri))
;;

let type_of_mutual_inductive_constr uri i j =
 let module C = Cic in
 let module R = CicReduction in
 let module U = UriManager in
  let cobj =
   match CicEnvironment.is_type_checked CicUniv.oblivion_ugraph uri with
      CicEnvironment.CheckedObj (cobj,_) -> cobj
    | CicEnvironment.UncheckedObj (uobj,_) ->
       raise (NotWellTyped "Reference to an unchecked constructor")
  in
   match cobj with
      C.InductiveDefinition (dl,_,_,_) ->
       let (_,_,_,cl) = List.nth dl i in
        let (_,ty) = List.nth cl (j-1) in
         ty
    | _ -> raise (WrongUriToMutualInductiveDefinitions (U.string_of_uri uri))
;;

let pack_coercion = ref (fun _ _ _ -> assert false);;

let profiler_for_find = HExtlib.profile "CicHash ADD" ;;

let cic_CicHash_add a b c =  
  profiler_for_find.HExtlib.profile (Cic.CicHash.add a b) c
;;

let profiler_for_find1 = HExtlib.profile "CicHash MEM" ;;

let cic_CicHash_mem a b =  
  profiler_for_find1.HExtlib.profile (Cic.CicHash.mem a) b
;;

(* type_of_aux' is just another name (with a different scope) for type_of_aux *)
let rec type_of_aux' subterms_to_types metasenv context t expectedty =
 (* Coscoy's double type-inference algorithm             *)
 (* It computes the inner-types of every subterm of [t], *)
 (* even when they are not needed to compute the types   *)
 (* of other terms.                                      *)
 let rec type_of_aux context t expectedty =
  let module C = Cic in
  let module R = CicReduction in
  let module S = CicSubstitution in
  let module U = UriManager in
   let expectedty =
    match expectedty with
       None -> None
     | Some t -> Some (!pack_coercion metasenv context t) in
   let synthesized =
    match t with
       C.Rel n ->
        (try
          match List.nth context (n - 1) with
             Some (_,C.Decl t) -> S.lift n t
           | Some (_,C.Def (_,ty)) -> S.lift n ty
	   | None -> raise RelToHiddenHypothesis
         with
          _ -> raise (NotWellTyped "Not a close term")
        )
     | C.Var (uri,exp_named_subst) ->
        visit_exp_named_subst context uri exp_named_subst ;
        CicSubstitution.subst_vars exp_named_subst (type_of_variable uri)
     | C.Meta (n,l) -> 
        (* Let's visit all the subterms that will not be visited later *)
        let (_,canonical_context,_) = CicUtil.lookup_meta n metasenv in
         let lifted_canonical_context =
          let rec aux i =
           function
              [] -> []
            | (Some (n,C.Decl t))::tl ->
               (Some (n,C.Decl (S.subst_meta l (S.lift i t))))::(aux (i+1) tl)
            | (Some (n,C.Def (t,ty)))::tl ->
               (Some (n,
                C.Def
                 ((S.subst_meta l (S.lift i t)),S.subst_meta l (S.lift i t))))::
                  (aux (i+1) tl)
            | None::tl -> None::(aux (i+1) tl)
          in
           aux 1 canonical_context
         in
          let _ =
           List.iter2
            (fun t ct ->
              match t,ct with
                 _,None -> ()
               | Some t,Some (_,C.Def (ct,_)) ->
                  let expected_type =
                    match xxx_type_of_aux' metasenv context ct with
                    | None -> None
                    | Some t -> Some (R.whd context t)
                  in
                   (* Maybe I am a bit too paranoid, because   *)
                   (* if the term is well-typed than t and ct  *)
                   (* are convertible. Nevertheless, I compute *)
                   (* the expected type.                       *)
                   ignore (type_of_aux context t expected_type)
               | Some t,Some (_,C.Decl ct) ->
                  ignore (type_of_aux context t (Some ct))
               | _,_ -> assert false (* the term is not well typed!!! *)
            ) l lifted_canonical_context
          in
           let (_,canonical_context,ty) = CicUtil.lookup_meta n metasenv in
            (* Checks suppressed *)
            CicSubstitution.subst_meta l ty
     | C.Sort (C.Type t) -> (* TASSI: CONSTRAINT *)
         C.Sort (C.Type (CicUniv.fresh()))
     | C.Sort _ -> C.Sort (C.Type (CicUniv.fresh())) (* TASSI: CONSTRAINT *)
     | C.Implicit _ -> raise (Impossible 21)
     | C.Cast (te,ty) ->
        (* Let's visit all the subterms that will not be visited later *)
        let _ = type_of_aux context te (Some (beta_reduce ty)) in
        let _ = type_of_aux context ty None in
         (* Checks suppressed *)
         ty
     | C.Prod (name,s,t) ->
        let sort1 = type_of_aux context s None
        and sort2 = type_of_aux ((Some (name,(C.Decl s)))::context) t None in
         sort_of_prod context (name,s) (sort1,sort2)
     | C.Lambda (n,s,t) ->
        (* Let's visit all the subterms that will not be visited later *)
         let _ = type_of_aux context s None in 
         let n, expected_target_type =
          match expectedty with
           | None -> n, None
           | Some expectedty' ->
              let n, ty =
               match R.whd context expectedty' with
                | C.Prod (n',_,expected_target_type) ->
                   let xtt = beta_reduce expected_target_type in
		   if n <> C.Anonymous then n, xtt else n', xtt
                | _ -> assert false
              in
               n, Some ty
         in 
          let type2 =
           type_of_aux ((Some (n,(C.Decl s)))::context) t expected_target_type
          in
           (* Checks suppressed *)
           C.Prod (n,s,type2)
     | C.LetIn (n,s,ty,t) ->
(*CSC: What are the right expected types for the source and *)
(*CSC: target of a LetIn? None used.                        *)
        (* Let's visit all the subterms that will not be visited later *)
        let _ = type_of_aux context ty None in
        let _ = type_of_aux context s (Some ty) in
         let t_typ =
          (* Checks suppressed *)
          type_of_aux ((Some (n,(C.Def (s,ty))))::context) t None
         in  (* CicSubstitution.subst s t_typ *)
	  if does_not_occur 1 t_typ then
	   (* since [Rel 1] does not occur in typ, substituting any term *)
           (* in place of [Rel 1] is equivalent to delifting once        *)
           CicSubstitution.subst (C.Implicit None) t_typ
          else
           C.LetIn (n,s,ty,t_typ)
     | C.Appl (he::tl) when List.length tl > 0 ->
        (* 
        let expected_hetype =
         (* Inefficient, the head is computed twice. But I know *)
         (* of no other solution. *)                               
         (beta_reduce
          (R.whd context (xxx_type_of_aux' metasenv context he)))
        in 
         let hetype = type_of_aux context he (Some expected_hetype) in 
         let tlbody_and_type =
          let rec aux =
           function
              _,[] -> []
            | C.Prod (n,s,t),he::tl ->
               (he, type_of_aux context he (Some (beta_reduce s)))::
                (aux (R.whd context (S.subst he t), tl))
            | _ -> assert false
          in
           aux (expected_hetype, tl) *)
         let hetype = R.whd context (type_of_aux context he None) in 
         let tlbody_and_type =
          let rec aux =
           function
              _,[] -> []
            | C.Prod (n,s,t),he::tl ->
               (he, type_of_aux context he (Some (beta_reduce s)))::
                (aux (R.whd context (S.subst he t), tl))
            | _ -> assert false
          in
           aux (hetype, tl)
         in
          eat_prods context hetype tlbody_and_type
     | C.Appl _ -> raise (NotWellTyped "Appl: no arguments")
     | C.Const (uri,exp_named_subst) ->
        visit_exp_named_subst context uri exp_named_subst ;
        CicSubstitution.subst_vars exp_named_subst (type_of_constant uri)
     | C.MutInd (uri,i,exp_named_subst) ->
        visit_exp_named_subst context uri exp_named_subst ;
        CicSubstitution.subst_vars exp_named_subst
         (type_of_mutual_inductive_defs uri i)
     | C.MutConstruct (uri,i,j,exp_named_subst) ->
        visit_exp_named_subst context uri exp_named_subst ;
        CicSubstitution.subst_vars exp_named_subst
         (type_of_mutual_inductive_constr uri i j)
     | C.MutCase (uri,i,outtype,term,pl) ->
        let outsort = type_of_aux context outtype None in
        let (need_dummy, k) =
         let rec guess_args context t =
          match CicReduction.whd context t with
             C.Sort _ -> (true, 0)
           | C.Prod (name, s, t) ->
              let (b, n) = guess_args ((Some (name,(C.Decl s)))::context) t in
               if n = 0 then
                (* last prod before sort *)
                match CicReduction.whd context s with
                   C.MutInd (uri',i',_) when U.eq uri' uri && i' = i ->
                    (false, 1)
                 | C.Appl ((C.MutInd (uri',i',_)) :: _)
                    when U.eq uri' uri && i' = i -> (false, 1)
                 | _ -> (true, 1)
               else
                (b, n + 1)
           | _ -> raise (NotWellTyped "MutCase: outtype ill-formed")
         in
          let (b, k) = guess_args context outsort in
           if not b then (b, k - 1) else (b, k)
        in
        let (parameters, arguments,exp_named_subst) =
         let type_of_term =
           match xxx_type_of_aux' metasenv context term with
           | None -> None
           | Some t -> Some (beta_reduce t)
         in
          match
           R.whd context (type_of_aux context term type_of_term)
          with
             (*CSC manca il caso dei CAST *)
             C.MutInd (uri',i',exp_named_subst) ->
              (* Checks suppressed *)
              [],[],exp_named_subst
           | C.Appl (C.MutInd (uri',i',exp_named_subst) :: tl) ->
             let params,args =
              split tl (List.length tl - k)
             in params,args,exp_named_subst
           | _ ->
             raise (NotWellTyped "MutCase: the term is not an inductive one")
        in
         (* Checks suppressed *)
         (* Let's visit all the subterms that will not be visited later *)
         let (cl,parsno) =
           let obj,_ =
             try
               CicEnvironment.get_cooked_obj CicUniv.oblivion_ugraph uri
             with Not_found -> assert false
           in
          match obj with
             C.InductiveDefinition (tl,_,parsno,_) ->
              let (_,_,_,cl) = List.nth tl i in (cl,parsno)
           | _ ->
             raise (WrongUriToMutualInductiveDefinitions (U.string_of_uri uri))
         in
          let _ =
           List.fold_left
            (fun j (p,(_,c)) ->
              let cons =
               if parameters = [] then
                (C.MutConstruct (uri,i,j,exp_named_subst))
               else
                (C.Appl (C.MutConstruct (uri,i,j,exp_named_subst)::parameters))
              in
               let expectedtype =
                 match xxx_type_of_aux' metasenv context cons with
                 | None -> None
                 | Some t -> 
                     Some 
                       (beta_reduce 
                         (type_of_branch context parsno need_dummy outtype 
                           cons t))
               in
                ignore (type_of_aux context p expectedtype);
                j+1
            ) 1 (List.combine pl cl)
          in
           if not need_dummy then
            C.Appl ((outtype::arguments)@[term])
           else if arguments = [] then
            outtype
           else
            C.Appl (outtype::arguments)
     | C.Fix (i,fl) ->
        (* Let's visit all the subterms that will not be visited later *)
        let context' =
         List.rev
          (List.map
            (fun (n,_,ty,_) ->
              let _ = type_of_aux context ty None in
               (Some (C.Name n,(C.Decl ty)))
            ) fl
          ) @
          context
        in
         let _ =
          List.iter
           (fun (_,_,ty,bo) ->
             let expectedty =
              beta_reduce (CicSubstitution.lift (List.length fl) ty)
             in
              ignore (type_of_aux context' bo (Some expectedty))
           ) fl
         in
          (* Checks suppressed *)
          let (_,_,ty,_) = List.nth fl i in
           ty
     | C.CoFix (i,fl) ->
        (* Let's visit all the subterms that will not be visited later *)
        let context' =
         List.rev
          (List.map
            (fun (n,ty,_) ->
              let _ = type_of_aux context ty None in
               (Some (C.Name n,(C.Decl ty)))
            ) fl
          ) @
          context
        in
         let _ =
          List.iter
           (fun (_,ty,bo) ->
             let expectedty =
              beta_reduce (CicSubstitution.lift (List.length fl) ty)
             in
              ignore (type_of_aux context' bo (Some expectedty))
           ) fl
         in
          (* Checks suppressed *)
          let (_,ty,_) = List.nth fl i in
           ty
   in
(* FG: beta-reduction can cause unreferenced letins *)
    let synthesized' = beta_reduce ~clean:true synthesized in
    let synthesized' = !pack_coercion metasenv context synthesized' in
     let types,res =
      match expectedty with
         None ->
          (* No expected type *)
          {synthesized = synthesized' ; expected = None}, synthesized
       | Some ty when CicUtil.alpha_equivalence synthesized' ty ->
          (* The expected type is synthactically equal to *)
          (* the synthesized type. Let's forget it.       *)
          {synthesized = synthesized' ; expected = None}, synthesized
       | Some expectedty' ->
          {synthesized = synthesized' ; expected = Some expectedty'},
          expectedty'
     in
(*      assert (not (cic_CicHash_mem subterms_to_types t));*)
      cic_CicHash_add subterms_to_types t types ;
      res

 and visit_exp_named_subst context uri exp_named_subst =
  let uris_and_types =
     let obj,_ =
       try
         CicEnvironment.get_cooked_obj CicUniv.oblivion_ugraph uri
       with Not_found -> assert false
     in
    let params = CicUtil.params_of_obj obj in
     List.map
      (function uri ->
         let obj,_ =
           try
             CicEnvironment.get_cooked_obj CicUniv.oblivion_ugraph uri
           with Not_found -> assert false
         in
         match obj with
           Cic.Variable (_,None,ty,_,_) -> uri,ty
         | _ -> assert false (* the theorem is well-typed *)
      ) params
  in
   let rec check uris_and_types subst =
    match uris_and_types,subst with
       _,[] -> ()
     | (uri,ty)::tytl,(uri',t)::substtl when uri = uri' ->
        ignore (type_of_aux context t (Some ty)) ;
        let tytl' =
         List.map
          (function uri,t' -> uri,(CicSubstitution.subst_vars [uri',t] t')) tytl
        in
         check tytl' substtl
     | _,_ -> assert false (* the theorem is well-typed *)
   in
    check uris_and_types exp_named_subst

 and sort_of_prod context (name,s) (t1, t2) =
  let module C = Cic in
   let t1' = CicReduction.whd context t1 in
   let t2' = CicReduction.whd ((Some (name,C.Decl s))::context) t2 in
   match (t1', t2') with
    | (C.Sort _, C.Sort s2) when (s2 = C.Prop || s2 = C.Set) -> C.Sort s2
    | (C.Sort (C.Type t1), C.Sort (C.Type t2)) ->C.Sort(C.Type(CicUniv.fresh()))
    | (C.Sort _,C.Sort (C.Type t1)) -> C.Sort (C.Type t1)
    | (C.Sort _,C.Sort (C.CProp t1)) -> C.Sort (C.CProp t1)
    | (C.Meta _, C.Sort _) -> t2'
    | (C.Meta _, (C.Meta (_,_) as t))
    | (C.Sort _, (C.Meta (_,_) as t)) when CicUtil.is_closed t ->
        t2'
    | (_,_) ->
      raise
       (NotWellTyped
        ("Prod: sort1= " ^ CicPp.ppterm t1' ^ " ; sort2= " ^ CicPp.ppterm t2'))

 and eat_prods context hetype =
  (*CSC: siamo sicuri che le are_convertible non lavorino con termini non *)
  (*CSC: cucinati                                                         *)
  function
     [] -> hetype
   | (hete, hety)::tl ->
    (match (CicReduction.whd context hetype) with
        Cic.Prod (n,s,t) ->
         (* Checks suppressed *)
         eat_prods context (CicSubstitution.subst hete t) tl
      | _ -> raise (NotWellTyped "Appl: wrong Prod-type")
    )

and type_of_branch context argsno need_dummy outtype term constype =
 let module C = Cic in
 let module R = CicReduction in
  match R.whd context constype with
     C.MutInd (_,_,_) ->
      if need_dummy then
       outtype
      else
       C.Appl [outtype ; term]
   | C.Appl (C.MutInd (_,_,_)::tl) ->
      let (_,arguments) = split tl argsno
      in
       if need_dummy && arguments = [] then
        outtype
       else
        C.Appl (outtype::arguments@(if need_dummy then [] else [term]))
   | C.Prod (name,so,de) ->
      let term' =
       match CicSubstitution.lift 1 term with
          C.Appl l -> C.Appl (l@[C.Rel 1])
        | t -> C.Appl [t ; C.Rel 1]
      in
       C.Prod (C.Anonymous,so,type_of_branch
        ((Some (name,(C.Decl so)))::context) argsno need_dummy
        (CicSubstitution.lift 1 outtype) term' de)
  | _ -> raise (Impossible 20)

 in
  type_of_aux context t expectedty
;;

let double_type_of metasenv context t expectedty =
 let subterms_to_types = Cic.CicHash.create 503 in
  ignore (type_of_aux' subterms_to_types metasenv context t expectedty) ;
  subterms_to_types
;;
