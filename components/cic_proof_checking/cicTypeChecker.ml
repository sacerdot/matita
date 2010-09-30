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

(* TODO factorize functions to frequent errors (e.g. "Unknwon mutual inductive
 * ...") *)

open Printf

exception AssertFailure of string Lazy.t;;
exception TypeCheckerFailure of string Lazy.t;;

let fdebug = ref 0;;
let debug t context =
 let rec debug_aux t i =
  let module C = Cic in
  let module U = UriManager in
   CicPp.ppobj (C.Variable ("DEBUG", None, t, [], [])) ^ "\n" ^ i
 in
  if !fdebug = 0 then
   raise (TypeCheckerFailure (lazy (List.fold_right debug_aux (t::context) "")))
;;

let debug_print = fun _ -> ();;

let rec split l n =
 match (l,n) with
    (l,0) -> ([], l)
  | (he::tl, n) -> let (l1,l2) = split tl (n-1) in (he::l1,l2)
  | (_,_) ->
      raise (TypeCheckerFailure (lazy "Parameters number < left parameters number"))
;;

(* XXX: bug *)
let ugraph_convertibility ug1 ug2 ul2 = true;;

let check_and_clean_ugraph inferred_ugraph unchecked_ugraph uri obj =
 match unchecked_ugraph with
 | Some (ug,ul) ->
     if not (ugraph_convertibility inferred_ugraph ug ul) then
       raise (TypeCheckerFailure (lazy 
         ("inferred univ graph not equal with declared ugraph")))
     else 
      ug,ul,obj
 | None -> 
     CicUnivUtils.clean_and_fill uri obj inferred_ugraph 
;;

let debrujin_constructor ?(cb=fun _ _ -> ()) ?(check_exp_named_subst=true) uri number_of_types context =
 let rec aux k t =
  let module C = Cic in
  let res =
   match t with
      C.Rel n as t when n <= k -> t
    | C.Rel _ ->
        raise (TypeCheckerFailure (lazy "unbound variable found in constructor type"))
    | C.Var (uri,exp_named_subst) ->
       let exp_named_subst' = 
        List.map (function (uri,t) -> (uri,aux k t)) exp_named_subst
       in
        C.Var (uri,exp_named_subst')
    | C.Meta (i,l) ->
       let l' = List.map (function None -> None | Some t -> Some (aux k t)) l in
        C.Meta (i,l')
    | C.Sort _
    | C.Implicit _ as t -> t
    | C.Cast (te,ty) -> C.Cast (aux k te, aux k ty)
    | C.Prod (n,s,t) -> C.Prod (n, aux k s, aux (k+1) t)
    | C.Lambda (n,s,t) -> C.Lambda (n, aux k s, aux (k+1) t)
    | C.LetIn (n,s,ty,t) -> C.LetIn (n, aux k s, aux k ty, aux (k+1) t)
    | C.Appl l -> C.Appl (List.map (aux k) l)
    | C.Const (uri,exp_named_subst) ->
       let exp_named_subst' = 
        List.map (function (uri,t) -> (uri,aux k t)) exp_named_subst
       in
        C.Const (uri,exp_named_subst')
    | C.MutInd (uri',tyno,exp_named_subst) when UriManager.eq uri uri' ->
       if check_exp_named_subst && exp_named_subst != [] then
        raise (TypeCheckerFailure
          (lazy ("non-empty explicit named substitution is applied to "^
           "a mutual inductive type which is being defined"))) ;
       C.Rel (k + number_of_types - tyno) ;
    | C.MutInd (uri',tyno,exp_named_subst) ->
       let exp_named_subst' = 
        List.map (function (uri,t) -> (uri,aux k t)) exp_named_subst
       in
        C.MutInd (uri',tyno,exp_named_subst')
    | C.MutConstruct (uri,tyno,consno,exp_named_subst) ->
       let exp_named_subst' = 
        List.map (function (uri,t) -> (uri,aux k t)) exp_named_subst
       in
        C.MutConstruct (uri,tyno,consno,exp_named_subst')
    | C.MutCase (sp,i,outty,t,pl) ->
       C.MutCase (sp, i, aux k outty, aux k t,
        List.map (aux k) pl)
    | C.Fix (i, fl) ->
       let len = List.length fl in
       let liftedfl =
        List.map
         (fun (name, i, ty, bo) -> (name, i, aux k ty, aux (k+len) bo))
          fl
       in
        C.Fix (i, liftedfl)
    | C.CoFix (i, fl) ->
       let len = List.length fl in
       let liftedfl =
        List.map
         (fun (name, ty, bo) -> (name, aux k ty, aux (k+len) bo))
          fl
       in
        C.CoFix (i, liftedfl)
  in
   cb t res;
   res
 in
  aux (List.length context)
;;

exception CicEnvironmentError;;

let check_homogeneous_call context indparamsno n uri reduct tl =
 let last =
  List.fold_left
   (fun k x ->
     if k = 0 then 0
     else
      match CicReduction.whd context x with
      | Cic.Rel m when m = n - (indparamsno - k) -> k - 1
      | _ -> raise (TypeCheckerFailure (lazy 
         ("Argument "^string_of_int (indparamsno - k + 1) ^ " (of " ^
         string_of_int indparamsno ^ " fixed) is not homogeneous in "^
         "appl:\n"^ CicPp.ppterm reduct))))
   indparamsno tl
 in
  if last <> 0 then
   raise (TypeCheckerFailure
    (lazy ("Non-positive occurence in mutual inductive definition(s) [2]"^
     UriManager.string_of_uri uri)))
;;


let rec type_of_constant ~logger uri orig_ugraph =
 let module C = Cic in
 let module R = CicReduction in
 let module U = UriManager in
 let cobj,ugraph =
   match CicEnvironment.is_type_checked ~trust:true orig_ugraph uri with
      CicEnvironment.CheckedObj (cobj,ugraph') -> cobj,ugraph'
    | CicEnvironment.UncheckedObj (uobj,unchecked_ugraph) ->
       logger#log (`Start_type_checking uri) ;
       (* let's typecheck the uncooked obj *)
       let inferred_ugraph = 
         match uobj with
           C.Constant (_,Some te,ty,_,_) ->
           let _,ugraph = type_of ~logger ty CicUniv.empty_ugraph in
           let type_of_te,ugraph = type_of ~logger te ugraph in
              let b,ugraph = R.are_convertible [] type_of_te ty ugraph in
              if not b then
               raise (TypeCheckerFailure (lazy (sprintf
                "the constant %s is not well typed because the type %s of the body is not convertible to the declared type %s"
                (U.string_of_uri uri) (CicPp.ppterm type_of_te)
                (CicPp.ppterm ty))))
              else
                ugraph
         | C.Constant (_,None,ty,_,_) ->
           (* only to check that ty is well-typed *)
           let _,ugraph = type_of ~logger ty CicUniv.empty_ugraph in 
           ugraph
         | C.CurrentProof (_,conjs,te,ty,_,_) ->
             let _,ugraph =
              List.fold_left
               (fun (metasenv,ugraph) ((_,context,ty) as conj) ->
                 let _,ugraph = 
                  type_of_aux' ~logger metasenv context ty ugraph 
                 in
                 (metasenv @ [conj],ugraph)
               ) ([],CicUniv.empty_ugraph) conjs
             in
             let _,ugraph = type_of_aux' ~logger conjs [] ty ugraph in
             let type_of_te,ugraph = type_of_aux' ~logger conjs [] te ugraph in
             let b,ugraph = R.are_convertible [] type_of_te ty ugraph in
               if not b then
                 raise (TypeCheckerFailure (lazy (sprintf
                  "the current proof %s is not well typed because the type %s of the body is not convertible to the declared type %s"
                  (U.string_of_uri uri) (CicPp.ppterm type_of_te)
                  (CicPp.ppterm ty))))
               else 
                 ugraph
         | _ ->
             raise
              (TypeCheckerFailure (lazy ("Unknown constant:" ^ U.string_of_uri uri)))
       in 
       let ugraph, ul, obj = check_and_clean_ugraph inferred_ugraph unchecked_ugraph uri uobj in
       CicEnvironment.set_type_checking_info uri (obj, ugraph, ul);
       logger#log (`Type_checking_completed uri) ;
       match CicEnvironment.is_type_checked ~trust:false orig_ugraph uri with
           CicEnvironment.CheckedObj (cobj,ugraph') -> cobj,ugraph'
         | CicEnvironment.UncheckedObj _ -> raise CicEnvironmentError
  in
   match cobj,ugraph with
      (C.Constant (_,_,ty,_,_)),g -> ty,g
    | (C.CurrentProof (_,_,_,ty,_,_)),g -> ty,g
    | _ ->
        raise (TypeCheckerFailure (lazy ("Unknown constant:" ^ U.string_of_uri uri)))

and type_of_variable ~logger uri orig_ugraph =
 let module C = Cic in
 let module R = CicReduction in
 let module U = UriManager in
  (* 0 because a variable is never cooked => no partial cooking at one level *)
  match CicEnvironment.is_type_checked ~trust:true orig_ugraph uri with
  | CicEnvironment.CheckedObj ((C.Variable (_,_,ty,_,_)),ugraph') -> ty,ugraph'
  | CicEnvironment.UncheckedObj 
     (C.Variable (_,bo,ty,_,_) as uobj, unchecked_ugraph) 
    ->
      logger#log (`Start_type_checking uri) ;
      (* only to check that ty is well-typed *)
      let _,ugraph = type_of ~logger ty CicUniv.empty_ugraph in
      let inferred_ugraph = 
       match bo with
           None -> ugraph
         | Some bo ->
             let ty_bo,ugraph = type_of ~logger bo ugraph in
             let b,ugraph = R.are_convertible [] ty_bo ty ugraph in
             if not b then
              raise (TypeCheckerFailure
                (lazy ("Unknown variable:" ^ U.string_of_uri uri)))
             else
               ugraph 
      in
       let ugraph, ul, obj = 
         check_and_clean_ugraph inferred_ugraph unchecked_ugraph uri uobj 
       in
       CicEnvironment.set_type_checking_info uri (obj, ugraph, ul);
       logger#log (`Type_checking_completed uri) ;
       (match CicEnvironment.is_type_checked ~trust:false orig_ugraph uri with
           CicEnvironment.CheckedObj((C.Variable(_,_,ty,_,_)),ugraph)->ty,ugraph
         | CicEnvironment.CheckedObj _ 
         | CicEnvironment.UncheckedObj _ -> raise CicEnvironmentError)
   |  _ ->
        raise (TypeCheckerFailure (lazy 
          ("Unknown variable:" ^ U.string_of_uri uri)))

and does_not_occur ?(subst=[]) context n nn te =
 let module C = Cic in
   match te with
      C.Rel m when m > n && m <= nn -> false
    | C.Rel m ->
       (try
         (match List.nth context (m-1) with
             Some (_,C.Def (bo,_)) ->
              does_not_occur ~subst context n nn (CicSubstitution.lift m bo)
           | _ -> true)
        with
         Failure _ -> assert false)
    | C.Sort _
    | C.Implicit _ -> true
    | C.Meta (mno,l) ->
       List.fold_right
        (fun x i ->
          match x with
             None -> i
           | Some x -> i && does_not_occur ~subst context n nn x) l true &&
       (try
         let (canonical_context,term,ty) = CicUtil.lookup_subst mno subst in
          does_not_occur ~subst context n nn (CicSubstitution.subst_meta l term)
        with
         CicUtil.Subst_not_found _ -> true)
    | C.Cast (te,ty) ->
       does_not_occur ~subst context n nn te && 
       does_not_occur ~subst context n nn ty
    | C.Prod (name,so,dest) ->
       does_not_occur ~subst context n nn so &&
        does_not_occur ~subst ((Some (name,(C.Decl so)))::context) (n + 1)
         (nn + 1) dest
    | C.Lambda (name,so,dest) ->
       does_not_occur ~subst context n nn so &&
        does_not_occur ~subst ((Some (name,(C.Decl so)))::context) (n+1) (nn+1)
         dest
    | C.LetIn (name,so,ty,dest) ->
       does_not_occur ~subst context n nn so &&
        does_not_occur ~subst context n nn ty &&
         does_not_occur ~subst ((Some (name,(C.Def (so,ty))))::context)
          (n + 1) (nn + 1) dest
    | C.Appl l ->
       List.for_all (does_not_occur ~subst context n nn) l
    | C.Var (_,exp_named_subst)
    | C.Const (_,exp_named_subst)
    | C.MutInd (_,_,exp_named_subst)
    | C.MutConstruct (_,_,_,exp_named_subst) ->
       List.for_all (fun (_,x) -> does_not_occur ~subst context n nn x)
        exp_named_subst
    | C.MutCase (_,_,out,te,pl) ->
       does_not_occur ~subst context n nn out && 
       does_not_occur ~subst context n nn te &&
       List.for_all (does_not_occur ~subst context n nn) pl
    | C.Fix (_,fl) ->
       let len = List.length fl in
        let n_plus_len = n + len in
        let nn_plus_len = nn + len in
        let tys,_ =
         List.fold_left
          (fun (types,len) (n,_,ty,_) ->
             (Some (C.Name n,(C.Decl (CicSubstitution.lift len ty)))::types,
              len+1)
          ) ([],0) fl
        in
         List.fold_right
          (fun (_,_,ty,bo) i ->
            i && does_not_occur ~subst context n nn ty &&
            does_not_occur ~subst (tys @ context) n_plus_len nn_plus_len bo
          ) fl true
    | C.CoFix (_,fl) ->
       let len = List.length fl in
        let n_plus_len = n + len in
        let nn_plus_len = nn + len in
        let tys,_ =
         List.fold_left
          (fun (types,len) (n,ty,_) ->
             (Some (C.Name n,(C.Decl (CicSubstitution.lift len ty)))::types,
              len+1)
          ) ([],0) fl
        in
         List.fold_right
          (fun (_,ty,bo) i ->
            i && does_not_occur ~subst context n nn ty &&
            does_not_occur ~subst (tys @ context) n_plus_len nn_plus_len bo
          ) fl true

(* Inductive types being checked for positivity have *)
(* indexes x s.t. n < x <= nn.                       *)
and weakly_positive context n nn uri indparamsno posuri te =
 let module C = Cic in
  (*CSC: Not very nice. *)
  let leftno = 
    match CicEnvironment.get_obj CicUniv.oblivion_ugraph uri with
    | Cic.InductiveDefinition (_,_,leftno,_), _ -> leftno
    | _ -> assert false
  in
  let dummy = Cic.Sort Cic.Prop in
  (*CSC: to be moved in cicSubstitution? *)
  let rec subst_inductive_type_with_dummy =
   function
      C.MutInd (uri',0,_) when UriManager.eq uri' uri ->
       dummy
    | C.Appl ((C.MutInd (uri',0,_))::tl) when UriManager.eq uri' uri ->
       let _, rargs = HExtlib.split_nth leftno tl in
       if rargs = [] then dummy else Cic.Appl (dummy :: rargs)
    | C.Cast (te,ty) -> subst_inductive_type_with_dummy te
    | C.Prod (name,so,ta) ->
       C.Prod (name, subst_inductive_type_with_dummy so,
        subst_inductive_type_with_dummy ta)
    | C.Lambda (name,so,ta) ->
       C.Lambda (name, subst_inductive_type_with_dummy so,
        subst_inductive_type_with_dummy ta)
    | C.LetIn (name,so,ty,ta) ->
       C.LetIn (name, subst_inductive_type_with_dummy so,
        subst_inductive_type_with_dummy ty,
        subst_inductive_type_with_dummy ta)
    | C.Appl tl ->
       C.Appl (List.map subst_inductive_type_with_dummy tl)
    | C.MutCase (uri,i,outtype,term,pl) ->
       C.MutCase (uri,i,
        subst_inductive_type_with_dummy outtype,
        subst_inductive_type_with_dummy term,
        List.map subst_inductive_type_with_dummy pl)
    | C.Fix (i,fl) ->
       C.Fix (i,List.map (fun (name,i,ty,bo) -> (name,i,
        subst_inductive_type_with_dummy ty,
        subst_inductive_type_with_dummy bo)) fl)
    | C.CoFix (i,fl) ->
       C.CoFix (i,List.map (fun (name,ty,bo) -> (name,
        subst_inductive_type_with_dummy ty,
        subst_inductive_type_with_dummy bo)) fl)
    | C.Const (uri,exp_named_subst) ->
       let exp_named_subst' =
        List.map
         (function (uri,t) -> (uri,subst_inductive_type_with_dummy t))
         exp_named_subst
       in
        C.Const (uri,exp_named_subst')
    | C.Var (uri,exp_named_subst) ->
       let exp_named_subst' =
        List.map
         (function (uri,t) -> (uri,subst_inductive_type_with_dummy t))
         exp_named_subst
       in
        C.Var (uri,exp_named_subst')
    | C.MutInd (uri,typeno,exp_named_subst) ->
       let exp_named_subst' =
        List.map
         (function (uri,t) -> (uri,subst_inductive_type_with_dummy t))
         exp_named_subst
       in
        C.MutInd (uri,typeno,exp_named_subst')
    | C.MutConstruct (uri,typeno,consno,exp_named_subst) ->
       let exp_named_subst' =
        List.map
         (function (uri,t) -> (uri,subst_inductive_type_with_dummy t))
         exp_named_subst
       in
        C.MutConstruct (uri,typeno,consno,exp_named_subst')
    | t -> t
  in
  (* this function has the same semantics of are_all_occurrences_positive
     but the i-th context entry role is played by dummy and some checks
     are skipped because we already know that are_all_occurrences_positive
     of uri in te. *)
  let rec aux context n nn te = 
    match CicReduction.whd context te with
     | C.Appl (C.Sort C.Prop::tl) -> 
         List.for_all (does_not_occur context n nn) tl
     | C.Sort C.Prop -> true
     | C.Prod (name,source,dest) when
        does_not_occur ((Some (name,(C.Decl source)))::context) 0 1 dest ->
         (* dummy abstraction, so we behave as in the anonimous case *)
         strictly_positive context n nn indparamsno posuri source &&
           aux ((Some (name,(C.Decl source)))::context)
           (n + 1) (nn + 1) dest
     | C.Prod (name,source,dest) ->
         does_not_occur context n nn source &&
           aux ((Some (name,(C.Decl source)))::context)
           (n + 1) (nn + 1) dest
     | _ ->
       raise (TypeCheckerFailure (lazy "Malformed inductive constructor type"))
 in 
   aux context n nn (subst_inductive_type_with_dummy te)

(* instantiate_parameters ps (x1:T1)...(xn:Tn)C                             *)
(* returns ((x_|ps|:T_|ps|)...(xn:Tn)C){ps_1 / x1 ; ... ; ps_|ps| / x_|ps|} *)
and instantiate_parameters params c =
 let module C = Cic in
  match (c,params) with
     (c,[]) -> c
   | (C.Prod (_,_,ta), he::tl) ->
       instantiate_parameters tl
        (CicSubstitution.subst he ta)
   | (C.Cast (te,_), _) -> instantiate_parameters params te
   | (t,l) -> raise (AssertFailure (lazy "1"))

and strictly_positive context n nn indparamsno posuri te =
 let module C = Cic in
 let module U = UriManager in
  match CicReduction.whd context te with
   | t when does_not_occur context n nn t -> true
   | C.Rel _ when indparamsno = 0 -> true
   | C.Cast (te,ty) ->
      (*CSC: bisogna controllare ty????*)
      strictly_positive context n nn indparamsno posuri te
   | C.Prod (name,so,ta) ->
      does_not_occur context n nn so &&
       strictly_positive ((Some (name,(C.Decl so)))::context) (n+1) (nn+1)
        indparamsno posuri ta
   | C.Appl ((C.Rel m)::tl) as reduct when m > n && m <= nn ->
      check_homogeneous_call context indparamsno n posuri reduct tl;
      List.fold_right (fun x i -> i && does_not_occur context n nn x) tl true
   | C.Appl ((C.MutInd (uri,i,exp_named_subst))::_) 
   | (C.MutInd (uri,i,exp_named_subst)) as t -> 
      let tl = match t with C.Appl (_::tl) -> tl | _ -> [] in
      let (ok,paramsno,ity,cl,name) =
        let o,_ = CicEnvironment.get_obj CicUniv.empty_ugraph uri in
          match o with
              C.InductiveDefinition (tl,_,paramsno,_) ->
                let (name,_,ity,cl) = List.nth tl i in
                (List.length tl = 1, paramsno, ity, cl, name) 
                (* (true, paramsno, ity, cl, name) *)
            | _ ->
                raise 
                  (TypeCheckerFailure
                     (lazy ("Unknown inductive type:" ^ U.string_of_uri uri)))
      in 
      let (params,arguments) = split tl paramsno in
      let lifted_params = List.map (CicSubstitution.lift 1) params in
      let cl' =
        List.map
          (fun (_,te) ->
             instantiate_parameters lifted_params
               (CicSubstitution.subst_vars exp_named_subst te)
          ) cl
      in
        ok &&
          List.fold_right
          (fun x i -> i && does_not_occur context n nn x)
          arguments true &&
          List.fold_right
          (fun x i ->
             i &&
               weakly_positive
                ((Some (C.Name name,(Cic.Decl ity)))::context) (n+1) (nn+1) uri
                indparamsno posuri x
          ) cl' true
   | t -> false
       
(* the inductive type indexes are s.t. n < x <= nn *)
and are_all_occurrences_positive context uri indparamsno i n nn te =
 let module C = Cic in
  match CicReduction.whd context te with
     C.Appl ((C.Rel m)::tl) as reduct when m = i ->
      check_homogeneous_call context indparamsno n uri reduct tl;
      List.fold_right (fun x i -> i && does_not_occur context n nn x) tl true
   | C.Rel m when m = i ->
      if indparamsno = 0 then
       true
      else
        raise (TypeCheckerFailure
         (lazy ("Non-positive occurence in mutual inductive definition(s) [3]"^
          UriManager.string_of_uri uri)))
   | C.Prod (name,source,dest) when
      does_not_occur ((Some (name,(C.Decl source)))::context) 0 1 dest ->
      (* dummy abstraction, so we behave as in the anonimous case *)
      strictly_positive context n nn indparamsno uri source &&
       are_all_occurrences_positive
        ((Some (name,(C.Decl source)))::context) uri indparamsno
        (i+1) (n + 1) (nn + 1) dest
   | C.Prod (name,source,dest) ->
      does_not_occur context n nn source &&
       are_all_occurrences_positive ((Some (name,(C.Decl source)))::context)
        uri indparamsno (i+1) (n + 1) (nn + 1) dest
   | _ ->
     raise
      (TypeCheckerFailure (lazy ("Malformed inductive constructor type " ^
        (UriManager.string_of_uri uri))))

(* Main function to checks the correctness of a mutual *)
(* inductive block definition. This is the function    *)
(* exported to the proof-engine.                       *)
and typecheck_mutual_inductive_defs ~logger uri (itl,_,indparamsno) ugraph =
 let module U = UriManager in
  (* let's check if the arity of the inductive types are well *)
  (* formed                                                   *)
  let ugrap1 = List.fold_left 
   (fun ugraph (_,_,x,_) -> let _,ugraph' = 
      type_of ~logger x ugraph in ugraph') 
   ugraph itl in

  (* let's check if the types of the inductive constructors  *)
  (* are well formed.                                        *)
  (* In order not to use type_of_aux we put the types of the *)
  (* mutual inductive types at the head of the types of the  *)
  (* constructors using Prods                                *)
  let len = List.length itl in
  let tys =
    List.rev_map (fun (n,_,ty,_) -> Some (Cic.Name n,(Cic.Decl ty))) itl in
  let _,ugraph2 =
    List.fold_right
      (fun (_,_,ty,cl) (i,ugraph) ->
        let _,ty_sort = split_prods ~subst:[] [] ~-1 ty in
        let ugraph'' = 
          List.fold_left
            (fun ugraph (name,te) -> 
              let te = debrujin_constructor uri len [] te in
              let context,te = split_prods ~subst:[] tys indparamsno te in
              let con_sort,ugraph = type_of_aux' ~logger [] context te ugraph in
              let ugraph =
               match
                CicReduction.whd context con_sort, CicReduction.whd [] ty_sort
               with
                  Cic.Sort (Cic.Type u1), Cic.Sort (Cic.Type u2) 
                | Cic.Sort (Cic.CProp u1), Cic.Sort (Cic.CProp u2) 
                | Cic.Sort (Cic.Type u1), Cic.Sort (Cic.CProp u2)
                | Cic.Sort (Cic.CProp u1), Cic.Sort (Cic.Type u2) ->
                   CicUniv.add_ge u2 u1 ugraph
                | Cic.Sort _, Cic.Sort Cic.Prop
                | Cic.Sort _, Cic.Sort Cic.CProp _
                | Cic.Sort _, Cic.Sort Cic.Set
                | Cic.Sort _, Cic.Sort Cic.Type _ -> ugraph
                | a,b ->
                   raise
                    (TypeCheckerFailure
                      (lazy ("Wrong constructor or inductive arity shape: "^
                        CicPp.ppterm a ^ " --- " ^ CicPp.ppterm b))) in
              (* let's check also the positivity conditions *)
              if
                not
                  (are_all_occurrences_positive context uri indparamsno
                    (i+indparamsno) indparamsno (len+indparamsno) te)
              then
                raise
                  (TypeCheckerFailure
                    (lazy ("Non positive occurence in " ^ U.string_of_uri uri))) 
              else
                ugraph
            ) ugraph cl in
        (i + 1),ugraph''
      ) itl (1,ugrap1)
  in
  ugraph2

(* Main function to checks the correctness of a mutual *)
(* inductive block definition.                         *)
and check_mutual_inductive_defs uri obj ugraph =
  match obj with
      Cic.InductiveDefinition (itl, params, indparamsno, _) ->
        typecheck_mutual_inductive_defs uri (itl,params,indparamsno) ugraph 
    | _ ->
        raise (TypeCheckerFailure (
                lazy ("Unknown mutual inductive definition:" ^
                 UriManager.string_of_uri uri)))

and type_of_mutual_inductive_defs ~logger uri i orig_ugraph =
 let module C = Cic in
 let module R = CicReduction in
 let module U = UriManager in
  let cobj,ugraph1 =
   match CicEnvironment.is_type_checked ~trust:true orig_ugraph uri with
       CicEnvironment.CheckedObj (cobj,ugraph') -> cobj,ugraph'
     | CicEnvironment.UncheckedObj (uobj,unchecked_ugraph) ->
         logger#log (`Start_type_checking uri) ;
         let inferred_ugraph = 
           check_mutual_inductive_defs ~logger uri uobj CicUniv.empty_ugraph 
         in
         let ugraph, ul, obj = check_and_clean_ugraph inferred_ugraph unchecked_ugraph uri uobj in
         CicEnvironment.set_type_checking_info uri (obj,ugraph,ul);
         logger#log (`Type_checking_completed uri) ;
         (match CicEnvironment.is_type_checked ~trust:false orig_ugraph uri with
              CicEnvironment.CheckedObj (cobj,ugraph') -> (cobj,ugraph')
            | CicEnvironment.UncheckedObj _ -> raise CicEnvironmentError
         )
  in
  match cobj with
  | C.InductiveDefinition (dl,_,_,_) ->
      let (_,_,arity,_) = List.nth dl i in
        arity,ugraph1
  | _ ->
     raise (TypeCheckerFailure
      (lazy ("Unknown mutual inductive definition:" ^ U.string_of_uri uri)))
            
and type_of_mutual_inductive_constr ~logger uri i j orig_ugraph =
 let module C = Cic in
 let module R = CicReduction in
 let module U = UriManager in
  let cobj,ugraph1 =
    match CicEnvironment.is_type_checked ~trust:true orig_ugraph uri with
        CicEnvironment.CheckedObj (cobj,ugraph') -> cobj,ugraph'
      | CicEnvironment.UncheckedObj (uobj,unchecked_ugraph) ->
          logger#log (`Start_type_checking uri) ;
          let inferred_ugraph = 
            check_mutual_inductive_defs ~logger uri uobj CicUniv.empty_ugraph 
          in
          let ugraph, ul, obj = check_and_clean_ugraph inferred_ugraph unchecked_ugraph uri uobj in
          CicEnvironment.set_type_checking_info uri (obj, ugraph, ul);
          logger#log (`Type_checking_completed uri) ;
          (match 
             CicEnvironment.is_type_checked ~trust:false orig_ugraph uri 
           with
                 CicEnvironment.CheckedObj (cobj,ugraph') -> cobj,ugraph' 
               | CicEnvironment.UncheckedObj _ -> 
                       raise CicEnvironmentError)
  in
    match cobj with
        C.InductiveDefinition (dl,_,_,_) ->
          let (_,_,_,cl) = List.nth dl i in
          let (_,ty) = List.nth cl (j-1) in
            ty,ugraph1
      | _ ->
          raise (TypeCheckerFailure
           (lazy ("Unknown mutual inductive definition:" ^ UriManager.string_of_uri uri)))

and recursive_args context n nn te =
 let module C = Cic in
 match CicReduction.whd context te with
    C.Rel _ 
  | C.MutInd _ -> []
  | C.Var _
  | C.Meta _
  | C.Sort _
  | C.Implicit _
  | C.Cast _ (*CSC ??? *) ->
     raise (AssertFailure (lazy "3")) (* due to type-checking *)
  | C.Prod (name,so,de) ->
     (not (does_not_occur context n nn so)) ::
      (recursive_args ((Some (name,(C.Decl so)))::context) (n+1) (nn + 1) de)
  | C.Lambda _
  | C.LetIn _ ->
     raise (AssertFailure (lazy "4")) (* due to type-checking *)
  | C.Appl _ -> []
  | C.Const _ -> raise (AssertFailure (lazy "5"))
  | C.MutConstruct _
  | C.MutCase _
  | C.Fix _
  | C.CoFix _ -> raise (AssertFailure (lazy "6")) (* due to type-checking *)

and get_new_safes ~subst context p rl safes n nn x =
 let module C = Cic in
 let module U = UriManager in
 let module R = CicReduction in
  match R.whd ~subst context p, rl with
   | C.Lambda (name,so,ta), b::tl ->
       let safes = List.map (fun x -> x + 1) safes in
       let safes = if b then 1::safes else safes in
       get_new_safes ~subst ((Some (name,(C.Decl so)))::context)
          ta tl safes (n+1) (nn+1) (x+1)
   | C.MutConstruct _ as e, _
   | (C.Rel _ as e), _
   | e, [] -> (e,safes,n,nn,x,context)
   | p,_::_ ->
      raise
       (AssertFailure (lazy
         (Printf.sprintf "Get New Safes: p=%s" (CicPp.ppterm p))))

and split_prods ~subst context n te =
 let module C = Cic in
 let module R = CicReduction in
  match (n, R.whd ~subst context te) with
     (0, _) -> context,te
   | (n, C.Sort _) when n <= 0 -> context,te
   | (n, C.Prod (name,so,ta)) ->
       split_prods ~subst ((Some (name,(C.Decl so)))::context) (n - 1) ta
   | (_, _) -> raise (AssertFailure (lazy "8"))

and eat_lambdas ~subst context n te =
 let module C = Cic in
 let module R = CicReduction in
  match (n, R.whd ~subst context te) with
     (0, _) -> (te, 0, context)
   | (n, C.Lambda (name,so,ta)) when n > 0 ->
      let (te, k, context') =
       eat_lambdas ~subst ((Some (name,(C.Decl so)))::context) (n - 1) ta
      in
       (te, k + 1, context')
   | (n, te) ->
       raise (AssertFailure (lazy (sprintf "9 (%d, %s)" n (CicPp.ppterm te))))

and specialize_inductive_type ~logger ~subst ~metasenv context t = 
  let ty,_= type_of_aux' ~logger ~subst metasenv context t CicUniv.oblivion_ugraph in
  match CicReduction.whd ~subst context ty with
  | Cic.MutInd (uri,_,exp) 
  | Cic.Appl (Cic.MutInd (uri,_,exp) :: _) as ty ->
      let args = match ty with Cic.Appl (_::tl) -> tl | _ -> [] in
      let o,_ = CicEnvironment.get_obj CicUniv.oblivion_ugraph uri in
      (match o with
      | Cic.InductiveDefinition (tl,_,paramsno,_) ->
          let left_args,_ = HExtlib.split_nth paramsno args in
          List.map (fun (name, isind, arity, cl) ->
            let arity = CicSubstitution.subst_vars exp arity in
            let arity = instantiate_parameters left_args arity in
            let cl =
              List.map
               (fun (id,ty) -> 
                 let ty = CicSubstitution.subst_vars exp ty in
                 id, instantiate_parameters left_args ty) 
               cl 
            in
            name, isind, arity, cl)
          tl, paramsno
      | _ -> assert false)
  | _ -> assert false

and check_is_really_smaller_arg 
  ~logger ~metasenv ~subst rec_uri rec_uri_len context n nn kl x safes te 
=
 let module C = Cic in
 let module U = UriManager in
 (*CSC: we could perform beta-iota(-zeta?) immediately, and
   delta only on-demand when it fails without *)
 match CicReduction.whd ~subst context te with
     C.Rel m when List.mem m safes -> true
   | C.Rel _ 
   | C.MutConstruct _
   | C.Const _
   | C.Var _ -> false
   | C.Appl (he::_) ->
        check_is_really_smaller_arg rec_uri rec_uri_len 
          ~logger ~metasenv ~subst context n nn kl x safes he
   | C.Lambda (name,ty,ta) ->
      check_is_really_smaller_arg rec_uri rec_uri_len 
        ~logger ~metasenv ~subst (Some (name,Cic.Decl ty)::context)
        (n+1) (nn+1) kl (x+1) (List.map (fun n -> n+1) safes) ta
   | C.MutCase (uri,i,outtype,term,pl) ->
      (match term with
      | C.Rel m | C.Appl ((C.Rel m)::_) when List.mem m safes || m = x ->
         let tys,_ = 
           specialize_inductive_type ~logger ~subst ~metasenv context term 
         in
         let tys_ctx,_ = 
           List.fold_left
             (fun (types,len) (n,_,ty,_) ->
               Some (C.Name n,(C.Decl (CicSubstitution.lift len ty)))::types,
               len+1) 
             ([],0) tys
         in
         let _,isinductive,_,cl = List.nth tys i in
         if not isinductive then
           List.for_all
            (check_is_really_smaller_arg rec_uri rec_uri_len 
              ~logger ~metasenv ~subst context n nn kl x safes)
            pl
         else
           List.for_all2
            (fun p (_,c) ->
              let rec_params =
               let c = 
                 debrujin_constructor ~check_exp_named_subst:false
                  rec_uri rec_uri_len context c in
               let len_ctx = List.length context in
               recursive_args (context@tys_ctx) len_ctx (len_ctx+rec_uri_len) c
              in
              let (e, safes',n',nn',x',context') =
                get_new_safes ~subst context p rec_params safes n nn x
              in
               check_is_really_smaller_arg rec_uri rec_uri_len 
                ~logger ~metasenv ~subst context' n' nn' kl x' safes' e
            ) pl cl
        | _ ->
          List.for_all
           (check_is_really_smaller_arg 
             rec_uri rec_uri_len ~logger ~metasenv ~subst 
             context n nn kl x safes) pl
      )
   | C.Fix (_, fl) ->
      let len = List.length fl in
       let n_plus_len = n + len
       and nn_plus_len = nn + len
       and x_plus_len = x + len
       and tys,_ =
        List.fold_left
          (fun (types,len) (n,_,ty,_) ->
             (Some (C.Name n,(C.Decl (CicSubstitution.lift len ty)))::types,
              len+1)
          ) ([],0) fl
       and safes' = List.map (fun x -> x + len) safes in
        List.for_all
         (fun (_,_,_,bo) ->
            check_is_really_smaller_arg 
              rec_uri rec_uri_len ~logger ~metasenv ~subst 
                (tys@context) n_plus_len nn_plus_len kl
             x_plus_len safes' bo
         ) fl
   | t ->
      raise (AssertFailure (lazy ("An inhabitant of an inductive type in normal form cannot have this shape: " ^ CicPp.ppterm t)))

and guarded_by_destructors 
  ~logger ~metasenv ~subst rec_uri rec_uri_len context n nn kl x safes t 
=
 let module C = Cic in
 let module U = UriManager in
  let t = CicReduction.whd ~delta:false ~subst context t in
  let res =
   match t with
     C.Rel m when m > n && m <= nn -> false
   | C.Rel m ->
      (match List.nth context (m-1) with
          Some (_,C.Decl _) -> true
        | Some (_,C.Def (bo,_)) ->
           guarded_by_destructors rec_uri rec_uri_len ~logger ~metasenv ~subst context n nn kl x safes
            (CicSubstitution.lift m bo)
        | None -> raise (TypeCheckerFailure (lazy "Reference to deleted hypothesis"))
      )
   | C.Meta _
   | C.Sort _
   | C.Implicit _ -> true
   | C.Cast (te,ty) ->
      guarded_by_destructors rec_uri rec_uri_len ~logger ~metasenv ~subst context n nn kl x safes te &&
       guarded_by_destructors rec_uri rec_uri_len ~logger ~metasenv ~subst context n nn kl x safes ty
   | C.Prod (name,so,ta) ->
      guarded_by_destructors rec_uri rec_uri_len ~logger ~metasenv ~subst context n nn kl x safes so &&
       guarded_by_destructors rec_uri rec_uri_len ~logger ~metasenv ~subst ((Some (name,(C.Decl so)))::context)
        (n+1) (nn+1) kl (x+1) (List.map (fun x -> x + 1) safes) ta
   | C.Lambda (name,so,ta) ->
      guarded_by_destructors rec_uri rec_uri_len ~logger ~metasenv ~subst context n nn kl x safes so &&
       guarded_by_destructors rec_uri rec_uri_len ~logger ~metasenv ~subst ((Some (name,(C.Decl so)))::context)
        (n+1) (nn+1) kl (x+1) (List.map (fun x -> x + 1) safes) ta
   | C.LetIn (name,so,ty,ta) ->
      guarded_by_destructors rec_uri rec_uri_len ~logger ~metasenv ~subst context n nn kl x safes so &&
       guarded_by_destructors rec_uri rec_uri_len ~logger ~metasenv ~subst context n nn kl x safes ty &&
        guarded_by_destructors rec_uri rec_uri_len ~logger ~metasenv ~subst ((Some (name,(C.Def (so,ty))))::context)
         (n+1) (nn+1) kl (x+1) (List.map (fun x -> x + 1) safes) ta
   | C.Appl ((C.Rel m)::tl) when m > n && m <= nn ->
      let k = List.nth kl (m - n - 1) in
       if not (List.length tl > k) then false
       else
        List.for_all
         (guarded_by_destructors rec_uri rec_uri_len ~logger ~metasenv ~subst context n nn kl x safes) tl &&
        check_is_really_smaller_arg 
          rec_uri rec_uri_len 
          ~logger ~metasenv ~subst context n nn kl x safes (List.nth tl k)
   | C.Var (_,exp_named_subst)
   | C.Const (_,exp_named_subst)
   | C.MutInd (_,_,exp_named_subst)
   | C.MutConstruct (_,_,_,exp_named_subst) ->
      List.for_all
       (fun (_,t) -> guarded_by_destructors rec_uri rec_uri_len ~logger ~metasenv ~subst context n nn kl x safes t)
       exp_named_subst 
   | C.MutCase (uri,i,outtype,term,pl) ->
      (match CicReduction.whd ~subst context term with
        | C.Rel m 
        | C.Appl ((C.Rel m)::_) as t when List.mem m safes || m = x ->
           let tl = match t with C.Appl (_::tl) -> tl | _ -> [] in
           List.for_all
             (guarded_by_destructors rec_uri rec_uri_len ~logger ~metasenv ~subst context n nn kl x safes)
             tl &&
           let tys,_ = 
             specialize_inductive_type ~logger ~subst ~metasenv context t
           in
           let tys_ctx,_ = 
             List.fold_left
               (fun (types,len) (n,_,ty,_) ->
                 Some (C.Name n,(C.Decl (CicSubstitution.lift len ty)))::types,
                 len+1) 
               ([],0) tys
           in
           let _,isinductive,_,cl = List.nth tys i in
            if not isinductive then
             guarded_by_destructors rec_uri rec_uri_len ~logger ~metasenv ~subst context n nn kl x safes outtype &&
              guarded_by_destructors rec_uri rec_uri_len ~logger ~metasenv ~subst context n nn kl x safes term &&
              List.for_all
               (guarded_by_destructors rec_uri rec_uri_len ~logger ~metasenv ~subst context n nn kl x safes)
               pl
            else
             guarded_by_destructors rec_uri rec_uri_len ~logger ~metasenv ~subst context n nn kl x safes outtype &&
             List.for_all2
              (fun p (_,c) ->
               let rec_params =
                let c = 
                 debrujin_constructor ~check_exp_named_subst:false 
                  rec_uri rec_uri_len context c in
                let len_ctx = List.length context in
                recursive_args (context@tys_ctx) len_ctx (len_ctx+rec_uri_len) c
               in
               let (e, safes',n',nn',x',context') =
                get_new_safes ~subst context p rec_params safes n nn x
               in
                guarded_by_destructors rec_uri rec_uri_len ~logger ~metasenv ~subst context' n' nn' kl x' safes' e
               ) pl cl
        | _ ->
          guarded_by_destructors rec_uri rec_uri_len ~logger ~metasenv ~subst context n nn kl x safes outtype &&
           guarded_by_destructors rec_uri rec_uri_len ~logger ~metasenv ~subst context n nn kl x safes term &&
           (*CSC: manca ??? il controllo sul tipo di term? *)
           List.fold_right
            (fun p i -> i && guarded_by_destructors rec_uri rec_uri_len ~logger ~metasenv ~subst context n nn kl x safes p)
            pl true
      )
   | C.Appl (C.Fix (fixno, fl)::_) | C.Fix (fixno,fl) as t->
      let l = match t with C.Appl (_::tl) -> tl | _ -> [] in
      let len = List.length fl in
      let n_plus_len = n + len in
      let nn_plus_len = nn + len in
      let x_plus_len = x + len in
      let tys,_ =
        List.fold_left
          (fun (types,len) (n,_,ty,_) ->
             (Some (C.Name n,(C.Decl (CicSubstitution.lift len ty)))::types,
              len+1)
          ) ([],0) fl in
       let safes' = List.map (fun x -> x + len) safes in
        List.for_all
         (guarded_by_destructors rec_uri rec_uri_len ~logger ~metasenv ~subst context n nn kl x safes) l &&
        snd (List.fold_left
         (fun (fixno',i) (_,recno,ty,bo) ->
           fixno'+1,
           i &&
           guarded_by_destructors rec_uri rec_uri_len ~logger ~metasenv ~subst context n nn kl x_plus_len safes' ty &&
           if
            fixno' = fixno &&
            List.length l > recno &&
            (*case where the recursive argument is already really_smaller *)
            check_is_really_smaller_arg 
              rec_uri rec_uri_len ~logger ~metasenv ~subst context n nn kl x safes
              (List.nth l recno)
           then
            let bo_without_lambdas,_,context =
             eat_lambdas ~subst (tys@context) (recno+1) bo
            in
             (* we assume the formal argument to be safe *)
             guarded_by_destructors rec_uri rec_uri_len ~logger ~metasenv ~subst context (n_plus_len+recno+1)
              (nn_plus_len+recno+1) kl (x_plus_len+recno+1)
              (1::List.map (fun x -> x+recno+1) safes')
              bo_without_lambdas
           else
            guarded_by_destructors rec_uri rec_uri_len ~logger ~metasenv ~subst (tys@context) n_plus_len nn_plus_len
             kl x_plus_len safes' bo
         ) (0,true) fl)
   | C.CoFix (_, fl) ->
      let len = List.length fl in
       let n_plus_len = n + len
       and nn_plus_len = nn + len
       and x_plus_len = x + len
       and tys,_ =
        List.fold_left
          (fun (types,len) (n,ty,_) ->
             (Some (C.Name n,(C.Decl (CicSubstitution.lift len ty)))::types,
              len+1)
          ) ([],0) fl
       and safes' = List.map (fun x -> x + len) safes in
        List.fold_right
         (fun (_,ty,bo) i ->
           i &&
            guarded_by_destructors rec_uri rec_uri_len ~logger ~metasenv ~subst context n nn kl x_plus_len safes' ty &&
            guarded_by_destructors rec_uri rec_uri_len ~logger ~metasenv ~subst (tys@context) n_plus_len nn_plus_len kl
             x_plus_len safes' bo
         ) fl true
   | C.Appl tl ->
      List.fold_right
       (fun t i -> i && guarded_by_destructors rec_uri rec_uri_len ~logger ~metasenv ~subst context n nn kl x safes t)
       tl true
  in
   if res then res
   else
    let t' = CicReduction.whd ~subst context t in
     if t = t' then
      false
     else
      guarded_by_destructors rec_uri rec_uri_len ~logger ~metasenv ~subst context n nn kl x safes t'

(* the boolean h means already protected *)
(* args is the list of arguments the type of the constructor that may be *)
(* found in head position must be applied to.                            *)
and guarded_by_constructors ~logger ~subst ~metasenv indURI =
 let module C = Cic in
 let rec aux context n nn h te =
  match CicReduction.whd ~subst context te with
   | C.Rel m when m > n && m <= nn -> h
   | C.Rel _ 
   | C.Meta _ -> true
   | C.Sort _
   | C.Implicit _
   | C.Cast _
   | C.Prod _
   | C.MutInd _ 
   | C.LetIn _ -> raise (AssertFailure (lazy "17"))
   | C.Lambda (name,so,de) ->
      does_not_occur ~subst context n nn so &&
      aux ((Some (name,(C.Decl so)))::context) (n + 1) (nn + 1) h de
   | C.Appl ((C.Rel m)::tl) when m > n && m <= nn ->
      h && List.for_all (does_not_occur ~subst context n nn) tl
   | C.MutConstruct (_,_,_,exp_named_subst) ->
      List.for_all 
        (fun (_,x) -> does_not_occur ~subst context n nn x) exp_named_subst
   | C.Appl ((C.MutConstruct (uri,i,j,exp_named_subst))::tl) as t ->
      List.for_all 
        (fun (_,x) -> does_not_occur ~subst context n nn x) exp_named_subst &&
      let consty, len_tys, tys_ctx, paramsno =
       let tys, paramsno = 
         specialize_inductive_type ~logger ~subst ~metasenv context t in
       let _,_,_,cl = List.nth tys i in  
       let _,ty = List.nth cl (j-1) in  
         ty, List.length tys,
         fst(List.fold_left
          (fun (types,len) (n,_,ty,_) ->
           Some (C.Name n,(C.Decl (CicSubstitution.lift len ty)))::types, len+1)
          ([],0) tys), paramsno
      in
      let rec_params =
       let c = 
         debrujin_constructor ~check_exp_named_subst:false
           indURI len_tys context consty 
       in
       let len_ctx = List.length context in
       recursive_args (context@tys_ctx) len_ctx (len_ctx+len_tys) c
      in
      let rec analyse_instantiated_type rec_spec args =
       match rec_spec, args with
       | h::rec_spec, he::args -> 
           aux context n nn h he &&
           analyse_instantiated_type rec_spec args 
       | _,[] -> true
       | _ -> raise (AssertFailure (lazy 
         ("Too many args for constructor: " ^ String.concat " "
         (List.map (fun x-> CicPp.ppterm x) args))))
      in
      let left, args = HExtlib.split_nth paramsno tl in
      List.for_all (does_not_occur ~subst context n nn) left &&
      analyse_instantiated_type rec_params args
   | C.Appl ((C.MutCase (_,_,out,te,pl))::_) 
   | C.MutCase (_,_,out,te,pl) as t ->
       let tl = match t with C.Appl (_::tl) -> tl | _ -> [] in
       List.for_all (does_not_occur ~subst context n nn) tl &&
       does_not_occur ~subst context n nn out &&
       does_not_occur ~subst context n nn te &&
       List.for_all (aux context n nn h ) pl
   | C.Fix (_,fl)
   | C.Appl (C.Fix (_,fl)::_) as t ->
       let tl = match t with C.Appl (_::tl) -> tl | _ -> [] in
      let len = List.length fl in
       let n_plus_len = n + len
       and nn_plus_len = nn + len
       and tys,_ =
        List.fold_left
          (fun (types,len) (n,_,ty,_) ->
             (Some (C.Name n,(C.Decl (CicSubstitution.lift len ty)))::types,
              len+1)
          ) ([],0) fl
       in
        List.for_all (does_not_occur ~subst context n nn) tl &&
        List.for_all
         (fun (_,_,ty,bo) ->
           does_not_occur ~subst context n nn ty &&
           aux (tys@context) n_plus_len nn_plus_len h bo)
         fl
   | C.Appl ((C.CoFix (_,fl))::_) 
   | C.CoFix (_,fl) as t ->
       let tl = match t with C.Appl (_::tl) -> tl | _ -> [] in
       let len = List.length fl in
       let n_plus_len = n + len
       and nn_plus_len = nn + len
       and tys,_ =
          List.fold_left
            (fun (types,len) (n,ty,_) ->
               (Some (C.Name n,(C.Decl (CicSubstitution.lift len ty)))::types,
                len+1)
            ) ([],0) fl
       in
       List.for_all (does_not_occur ~subst context n nn) tl &&
       List.for_all 
         (fun (_,ty,bo) ->
            does_not_occur ~subst context n nn ty &&
            aux (tys@context) n_plus_len nn_plus_len h bo) 
         fl
   | C.Var _
   | C.Const _
   | C.Appl _ as t -> does_not_occur ~subst context n nn t
 in
   aux 

and is_non_recursive ctx paramsno t uri =
  let t = debrujin_constructor uri 1 [] t in
(*   let ctx, t =  split_prods ~subst:[] ctx paramsno t in *)
  let len = List.length ctx in
  let rec aux ctx n nn t =
    match CicReduction.whd ctx t with
    | Cic.Prod (name,src,tgt) -> 
        does_not_occur ctx n nn src &&
         aux (Some (name,Cic.Decl src) :: ctx) (n+1) (nn+1) tgt
    | (Cic.Rel k) 
    | Cic.Appl (Cic.Rel k :: _) when k = nn -> true
    | t -> assert false
  in
    aux ctx (len-1) len t

and check_allowed_sort_elimination ~subst ~metasenv ~logger context uri i
  need_dummy ind arity1 arity2 ugraph =
 let module C = Cic in
 let module U = UriManager in
  let arity1 = CicReduction.whd ~subst context arity1 in
  let rec check_allowed_sort_elimination_aux ugraph context arity2 need_dummy =
   match arity1, CicReduction.whd ~subst context arity2 with
     (C.Prod (name,so1,de1), C.Prod (_,so2,de2)) ->
       let b,ugraph1 =
        CicReduction.are_convertible ~subst ~metasenv context so1 so2 ugraph in
       if b then
         check_allowed_sort_elimination ~subst ~metasenv ~logger 
           ((Some (name,C.Decl so1))::context) uri i
          need_dummy (C.Appl [CicSubstitution.lift 1 ind ; C.Rel 1]) de1 de2
          ugraph1
       else
         false,ugraph1
   | (C.Sort _, C.Prod (name,so,ta)) when not need_dummy ->
       let b,ugraph1 =
        CicReduction.are_convertible ~subst ~metasenv context so ind ugraph in
       if not b then
         false,ugraph1
       else
        check_allowed_sort_elimination_aux ugraph1
         ((Some (name,C.Decl so))::context) ta true
   | (C.Sort C.Prop, C.Sort C.Prop) when need_dummy -> true,ugraph
   | (C.Sort C.Prop, C.Sort C.Set)
   | (C.Sort C.Prop, C.Sort (C.CProp _))
   | (C.Sort C.Prop, C.Sort (C.Type _) ) when need_dummy ->
       (let o,_ = CicEnvironment.get_obj CicUniv.empty_ugraph uri in
         match o with
         C.InductiveDefinition (itl,_,paramsno,_) ->
           let itl_len = List.length itl in
           let (name,_,ty,cl) = List.nth itl i in
           let cl_len = List.length cl in
            if (cl_len = 0 || (itl_len = 1 && cl_len = 1)) then
             let non_informative,ugraph =
              if cl_len = 0 then true,ugraph
              else
               let b, ug =
                is_non_informative ~logger [Some (C.Name name,C.Decl ty)]
                 paramsno (snd (List.nth cl 0)) ugraph
               in
                b && 
                is_non_recursive [Some (C.Name name,C.Decl ty)]
                  paramsno  (snd (List.nth cl 0)) uri, ug
             in
              (* is it a singleton or empty non recursive and non informative
                 definition? *)
              non_informative, ugraph
            else
              false,ugraph
         | _ ->
             raise (TypeCheckerFailure 
                     (lazy ("Unknown mutual inductive definition:" ^
                       UriManager.string_of_uri uri)))
       )
   | (C.Sort C.Set, C.Sort C.Prop) when need_dummy -> true , ugraph
   | (C.Sort C.Set, C.Sort C.Set) when need_dummy -> true , ugraph
   | (C.Sort C.Set, C.Sort (C.Type _)) 
   | (C.Sort C.Set, C.Sort (C.CProp _))
      when need_dummy ->
       (let o,_ = CicEnvironment.get_obj CicUniv.empty_ugraph uri in
         match o with
           C.InductiveDefinition (itl,_,paramsno,_) ->
            let tys =
             List.map (fun (n,_,ty,_) -> Some (Cic.Name n,(Cic.Decl ty))) itl
            in
             let (_,_,_,cl) = List.nth itl i in
              (List.fold_right
               (fun (_,x) (i,ugraph) -> 
                 if i then
                          is_small ~logger tys paramsno x ugraph
                 else
                   false,ugraph
                    ) cl (true,ugraph))
           | _ ->
            raise (TypeCheckerFailure
             (lazy ("Unknown mutual inductive definition:" ^
              UriManager.string_of_uri uri)))
       )
   | (C.Sort (C.Type _), C.Sort _) when need_dummy -> true , ugraph
   | (C.Sort (C.CProp _), C.Sort _) when need_dummy -> true , ugraph
   | (_,_) -> false,ugraph
 in
  check_allowed_sort_elimination_aux ugraph context arity2 need_dummy
         
and type_of_branch ~subst context argsno need_dummy outtype term constype =
 let module C = Cic in
 let module R = CicReduction in
  match R.whd ~subst context constype with
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
       C.Prod (name,so,type_of_branch ~subst
        ((Some (name,(C.Decl so)))::context) argsno need_dummy
        (CicSubstitution.lift 1 outtype) term' de)
   | _ -> raise (AssertFailure (lazy "20"))

(* check_metasenv_consistency checks that the "canonical" context of a
metavariable is consitent - up to relocation via the relocation list l -
with the actual context *)


and check_metasenv_consistency ~logger ~subst metasenv context 
  canonical_context l ugraph 
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
           (Some (n,C.Def ((S.subst_meta l (S.lift i t)),S.subst_meta l (S.lift i ty))))::(aux (i+1) tl)
    in
     aux 1 canonical_context
   in
   List.fold_left2 
     (fun ugraph t ct -> 
       match (t,ct) with
       | _,None -> ugraph
       | Some t,Some (_,C.Def (ct,_)) ->
          (*CSC: the following optimization is to avoid a possibly expensive
                 reduction that can be easily avoided and that is quite
                 frequent. However, this is better handled using levels to
                 control reduction *)
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
(*if t <> optimized_t && optimized_t = ct then prerr_endline "!!!!!!!!!!!!!!!"
else if t <> optimized_t then prerr_endline ("@@ " ^ CicPp.ppterm t ^ " ==> " ^ CicPp.ppterm optimized_t ^ " <==> " ^ CicPp.ppterm ct);*)
           let b,ugraph1 = 
             R.are_convertible ~subst ~metasenv context optimized_t ct ugraph 
           in
           if not b then
             raise 
               (TypeCheckerFailure 
                  (lazy (sprintf "Not well typed metavariable local context: expected a term convertible with %s, found %s" (CicPp.ppterm ct) (CicPp.ppterm t))))
           else
             ugraph1
       | Some t,Some (_,C.Decl ct) ->
           let type_t,ugraph1 = 
             type_of_aux' ~logger ~subst metasenv context t ugraph 
           in
           let b,ugraph2 = 
             R.are_convertible ~subst ~metasenv context type_t ct ugraph1 
           in
           if not b then
             raise (TypeCheckerFailure 
                     (lazy (sprintf "Not well typed metavariable local context: expected a term of type %s, found %s of type %s" 
                         (CicPp.ppterm ct) (CicPp.ppterm t)
                         (CicPp.ppterm type_t))))
           else
             ugraph2
       | None, _  ->
           raise (TypeCheckerFailure
                   (lazy ("Not well typed metavariable local context: "^
                     "an hypothesis, that is not hidden, is not instantiated")))
     ) ugraph l lifted_canonical_context 
     

(* 
   type_of_aux' is just another name (with a different scope) 
   for type_of_aux 
*)

and type_of_aux' ~logger ?(subst = []) metasenv context t ugraph =
 let rec type_of_aux ~logger context t ugraph =
  let module C = Cic in
  let module R = CicReduction in
  let module S = CicSubstitution in
  let module U = UriManager in
(* FG: DEBUG ONLY   
   prerr_endline ("TC: context:\n" ^ CicPp.ppcontext ~metasenv context);
   prerr_endline ("TC: term   :\n" ^ CicPp.ppterm ~metasenv t ^ "\n");
*)   
   match t with
      C.Rel n ->
       (try
         match List.nth context (n - 1) with
            Some (_,C.Decl t) -> S.lift n t,ugraph
          | Some (_,C.Def (_,ty)) -> S.lift n ty,ugraph
          | None -> raise 
              (TypeCheckerFailure (lazy "Reference to deleted hypothesis"))
        with
        Failure _ ->
          raise (TypeCheckerFailure (lazy "unbound variable"))
       )
    | C.Var (uri,exp_named_subst) ->
      incr fdebug ;
        let ugraph1 = 
          check_exp_named_subst uri ~logger ~subst context exp_named_subst ugraph 
        in 
        let ty,ugraph2 = type_of_variable ~logger uri ugraph1 in
        let ty1 = CicSubstitution.subst_vars exp_named_subst ty in
          decr fdebug ;
          ty1,ugraph2
    | C.Meta (n,l) -> 
       (try
          let (canonical_context,term,ty) = CicUtil.lookup_subst n subst in
          let ugraph1 =
            check_metasenv_consistency ~logger
              ~subst metasenv context canonical_context l ugraph
          in
            (* assuming subst is well typed !!!!! *)
            ((CicSubstitution.subst_meta l ty), ugraph1)
              (* type_of_aux context (CicSubstitution.subst_meta l term) *)
        with CicUtil.Subst_not_found _ ->
          let (_,canonical_context,ty) = CicUtil.lookup_meta n metasenv in
          let ugraph1 = 
            check_metasenv_consistency ~logger
              ~subst metasenv context canonical_context l ugraph
          in
            ((CicSubstitution.subst_meta l ty),ugraph1))
      (* TASSI: CONSTRAINTS *)
    | C.Sort (C.CProp t) -> 
       let t' = CicUniv.fresh() in
       (try
         let ugraph1 = CicUniv.add_gt t' t ugraph in
           (C.Sort (C.Type t')),ugraph1
        with
         CicUniv.UniverseInconsistency msg -> raise (TypeCheckerFailure msg))
    | C.Sort (C.Type t) -> 
       let t' = CicUniv.fresh() in
       (try
         let ugraph1 = CicUniv.add_gt t' t ugraph in
           (C.Sort (C.Type t')),ugraph1
        with
         CicUniv.UniverseInconsistency msg -> raise (TypeCheckerFailure msg))
    | C.Sort (C.Prop|C.Set) -> (C.Sort (C.Type (CicUniv.fresh ()))),ugraph
    | C.Implicit _ -> raise (AssertFailure (lazy "Implicit found"))
    | C.Cast (te,ty) as t ->
       let _,ugraph1 = type_of_aux ~logger context ty ugraph in
       let ty_te,ugraph2 = type_of_aux ~logger context te ugraph1 in
       let b,ugraph3 = 
         R.are_convertible ~subst ~metasenv context ty_te ty ugraph2 
       in
         if b then
           ty,ugraph3
         else
           raise (TypeCheckerFailure
                    (lazy (sprintf "Invalid cast %s" (CicPp.ppterm t))))
    | C.Prod (name,s,t) ->
       let sort1,ugraph1 = type_of_aux ~logger context s ugraph in
       let sort2,ugraph2 = 
         type_of_aux ~logger  ((Some (name,(C.Decl s)))::context) t ugraph1 
       in
       sort_of_prod ~subst context (name,s) (sort1,sort2) ugraph2
   | C.Lambda (n,s,t) ->
       let sort1,ugraph1 = type_of_aux ~logger context s ugraph in
       (match R.whd ~subst context sort1 with
           C.Meta _
         | C.Sort _ -> ()
         | _ ->
           raise
            (TypeCheckerFailure (lazy (sprintf
              "Not well-typed lambda-abstraction: the source %s should be a type; instead it is a term of type %s" (CicPp.ppterm s)
                (CicPp.ppterm sort1))))
       ) ;
       let type2,ugraph2 = 
         type_of_aux ~logger ((Some (n,(C.Decl s)))::context) t ugraph1 
       in
         (C.Prod (n,s,type2)),ugraph2
   | C.LetIn (n,s,ty,t) ->
      (* only to check if s is well-typed *)
      let ty',ugraph1 = type_of_aux ~logger context s ugraph in
      let _,ugraph1 = type_of_aux ~logger context ty ugraph1 in
      let b,ugraph1 =
       R.are_convertible ~subst ~metasenv context ty' ty ugraph1
      in 
       if not b then
        raise 
         (TypeCheckerFailure 
           (lazy (sprintf
             "The type of %s is %s but it is expected to be %s" 
               (CicPp.ppterm s) (CicPp.ppterm ty') (CicPp.ppterm ty))))
       else
       (* The type of a LetIn is a LetIn. Extremely slow since the computed
          LetIn is later reduced and maybe also re-checked.
       (C.LetIn (n,s, type_of_aux ((Some (n,(C.Def s)))::context) t))
       *)
       (* The type of the LetIn is reduced. Much faster than the previous
          solution. Moreover the inferred type is probably very different
          from the expected one.
       (CicReduction.whd ~subst context
        (C.LetIn (n,s, type_of_aux ((Some (n,(C.Def s)))::context) t)))
       *)
       (* One-step LetIn reduction. Even faster than the previous solution.
          Moreover the inferred type is closer to the expected one. *)
       let ty1,ugraph2 = 
         type_of_aux ~logger 
           ((Some (n,(C.Def (s,ty))))::context) t ugraph1 
       in
       (CicSubstitution.subst ~avoid_beta_redexes:true s ty1),ugraph2
   | C.Appl (he::tl) when List.length tl > 0 ->
       let hetype,ugraph1 = type_of_aux ~logger context he ugraph in
       let tlbody_and_type,ugraph2 = 
         List.fold_right (
           fun x (l,ugraph) -> 
             let ty,ugraph1 = type_of_aux ~logger context x ugraph in
             (*let _,ugraph1 = type_of_aux ~logger  context ty ugraph1 in*)
               ((x,ty)::l,ugraph1)) 
           tl ([],ugraph1) 
       in
         (* TASSI: questa c'era nel mio... ma non nel CVS... *)
         (* let _,ugraph2 = type_of_aux context hetype ugraph2 in *)
         eat_prods ~subst context hetype tlbody_and_type ugraph2
   | C.Appl _ -> raise (AssertFailure (lazy "Appl: no arguments"))
   | C.Const (uri,exp_named_subst) ->
       incr fdebug ;
       let ugraph1 = 
         check_exp_named_subst uri ~logger ~subst  context exp_named_subst ugraph 
       in
       let cty,ugraph2 = type_of_constant ~logger uri ugraph1 in
       let cty1 =
         CicSubstitution.subst_vars exp_named_subst cty
       in
         decr fdebug ;
         cty1,ugraph2
   | C.MutInd (uri,i,exp_named_subst) ->
      incr fdebug ;
       let ugraph1 = 
         check_exp_named_subst uri ~logger  ~subst context exp_named_subst ugraph 
       in
       let mty,ugraph2 = type_of_mutual_inductive_defs ~logger uri i ugraph1 in
       let cty =
         CicSubstitution.subst_vars exp_named_subst mty
       in
         decr fdebug ;
         cty,ugraph2
   | C.MutConstruct (uri,i,j,exp_named_subst) ->
       let ugraph1 = 
         check_exp_named_subst uri ~logger ~subst context exp_named_subst ugraph
       in
       let mty,ugraph2 = 
         type_of_mutual_inductive_constr ~logger uri i j ugraph1 
       in
       let cty =
         CicSubstitution.subst_vars exp_named_subst mty
       in
         cty,ugraph2
   | C.MutCase (uri,i,outtype,term,pl) ->
      let outsort,ugraph1 = type_of_aux ~logger context outtype ugraph in
      let (need_dummy, k) =
      let rec guess_args context t =
        let outtype = CicReduction.whd ~subst context t in
          match outtype with
              C.Sort _ -> (true, 0)
            | C.Prod (name, s, t) ->
                let (b, n) = 
                  guess_args ((Some (name,(C.Decl s)))::context) t in
                  if n = 0 then
                  (* last prod before sort *)
                    match CicReduction.whd ~subst context s with
(*CSC: for _ see comment below about the missing named_exp_subst ?????????? *)
                        C.MutInd (uri',i',_) when U.eq uri' uri && i' = i ->
                          (false, 1)
(*CSC: for _ see comment below about the missing named_exp_subst ?????????? *)
                      | C.Appl ((C.MutInd (uri',i',_)) :: _)
                          when U.eq uri' uri && i' = i -> (false, 1)
                      | _ -> (true, 1)
                  else
                    (b, n + 1)
            | _ ->
                raise 
                  (TypeCheckerFailure 
                     (lazy (sprintf
                        "Malformed case analasys' output type %s" 
                        (CicPp.ppterm outtype))))
      in
(*
      let (parameters, arguments, exp_named_subst),ugraph2 =
        let ty,ugraph2 = type_of_aux context term ugraph1 in
          match R.whd ~subst context ty with
           (*CSC manca il caso dei CAST *)
(*CSC: ma servono i parametri (uri,i)? Se si', perche' non serve anche il *)
(*CSC: parametro exp_named_subst? Se no, perche' non li togliamo?         *)
(*CSC: Hint: nella DTD servono per gli stylesheet.                        *)
              C.MutInd (uri',i',exp_named_subst) as typ ->
                if U.eq uri uri' && i = i' then 
                  ([],[],exp_named_subst),ugraph2
                else 
                  raise 
                    (TypeCheckerFailure 
                      (lazy (sprintf
                          ("Case analysys: analysed term type is %s, but is expected to be (an application of) %s#1/%d{_}")
                          (CicPp.ppterm typ) (U.string_of_uri uri) i)))
            | C.Appl 
                ((C.MutInd (uri',i',exp_named_subst) as typ):: tl) as typ' ->
                if U.eq uri uri' && i = i' then
                  let params,args =
                    split tl (List.length tl - k)
                  in (params,args,exp_named_subst),ugraph2
                else 
                  raise 
                    (TypeCheckerFailure 
                      (lazy (sprintf 
                          ("Case analysys: analysed term type is %s, "^
                           "but is expected to be (an application of) "^
                           "%s#1/%d{_}")
                          (CicPp.ppterm typ') (U.string_of_uri uri) i)))
            | _ ->
                raise 
                  (TypeCheckerFailure 
                    (lazy (sprintf
                        ("Case analysis: "^
                         "analysed term %s is not an inductive one")
                        (CicPp.ppterm term))))
*)
      let (b, k) = guess_args context outsort in
          if not b then (b, k - 1) else (b, k) in
      let (parameters, arguments, exp_named_subst),ugraph2 =
        let ty,ugraph2 = type_of_aux ~logger context term ugraph1 in
        match R.whd ~subst context ty with
            C.MutInd (uri',i',exp_named_subst) as typ ->
              if U.eq uri uri' && i = i' then 
                ([],[],exp_named_subst),ugraph2
              else raise 
                (TypeCheckerFailure 
                  (lazy (sprintf
                      ("Case analysys: analysed term type is %s (%s#1/%d{_}), but is expected to be (an application of) %s#1/%d{_}")
                      (CicPp.ppterm typ) (U.string_of_uri uri') i' (U.string_of_uri uri) i)))
          | C.Appl ((C.MutInd (uri',i',exp_named_subst) as typ):: tl) ->
              if U.eq uri uri' && i = i' then
                let params,args =
                  split tl (List.length tl - k)
                in (params,args,exp_named_subst),ugraph2
              else raise 
                (TypeCheckerFailure 
                  (lazy (sprintf
                      ("Case analysys: analysed term type is %s (%s#1/%d{_}), but is expected to be (an application of) %s#1/%d{_}")
                      (CicPp.ppterm typ) (U.string_of_uri uri') i' (U.string_of_uri uri) i)))
          | _ ->
              raise 
                (TypeCheckerFailure 
                  (lazy (sprintf
                      "Case analysis: analysed term %s is not an inductive one"
                      (CicPp.ppterm term))))
      in
        (* 
           let's control if the sort elimination is allowed: 
           [(I q1 ... qr)|B] 
        *)
      let sort_of_ind_type =
        if parameters = [] then
          C.MutInd (uri,i,exp_named_subst)
        else
          C.Appl ((C.MutInd (uri,i,exp_named_subst))::parameters)
      in
      let type_of_sort_of_ind_ty,ugraph3 = 
        type_of_aux ~logger context sort_of_ind_type ugraph2 in
      let b,ugraph4 = 
        check_allowed_sort_elimination ~subst ~metasenv ~logger  context uri i
          need_dummy sort_of_ind_type type_of_sort_of_ind_ty outsort ugraph3 
      in
        if not b then
        raise
          (TypeCheckerFailure (lazy ("Case analysis: sort elimination not allowed")));
        (* let's check if the type of branches are right *)
      let parsno,constructorsno =
        let obj,_ =
          try
            CicEnvironment.get_cooked_obj ~trust:false CicUniv.empty_ugraph uri
          with Not_found -> assert false
        in
        match obj with
            C.InductiveDefinition (il,_,parsno,_) ->
             let _,_,_,cl =
              try List.nth il i with Failure _ -> assert false
             in
              parsno, List.length cl
          | _ ->
              raise (TypeCheckerFailure
                (lazy ("Unknown mutual inductive definition:" ^
                  UriManager.string_of_uri uri)))
      in
      if List.length pl <> constructorsno then
       raise (TypeCheckerFailure
        (lazy ("Wrong number of cases in case analysis"))) ;
      let (_,branches_ok,ugraph5) =
        List.fold_left
          (fun (j,b,ugraph) p ->
            if b then
              let cons =
                if parameters = [] then
                  (C.MutConstruct (uri,i,j,exp_named_subst))
                else
                  (C.Appl 
                     (C.MutConstruct (uri,i,j,exp_named_subst)::parameters))
              in
              let ty_p,ugraph1 = type_of_aux ~logger context p ugraph in
              let ty_cons,ugraph3 = type_of_aux ~logger context cons ugraph1 in
              (* 2 is skipped *)
              let ty_branch = 
                type_of_branch ~subst context parsno need_dummy outtype cons 
                  ty_cons in
              let b1,ugraph4 =
                R.are_convertible 
                  ~subst ~metasenv context ty_p ty_branch ugraph3 
              in 
(* Debugging code
if not b1 then
begin
prerr_endline ("\n!OUTTYPE= " ^ CicPp.ppterm outtype);
prerr_endline ("!CONS= " ^ CicPp.ppterm cons);
prerr_endline ("!TY_CONS= " ^ CicPp.ppterm ty_cons);
prerr_endline ("#### " ^ CicPp.ppterm ty_p ^ "\n<==>\n" ^ CicPp.ppterm ty_branch);
end;
*)
              if not b1 then
                debug_print (lazy
                  ("#### " ^ CicPp.ppterm ty_p ^ 
                  " <==> " ^ CicPp.ppterm ty_branch));
              (j + 1,b1,ugraph4)
            else
              (j,false,ugraph)
          ) (1,true,ugraph4) pl
         in
          if not branches_ok then
           raise
            (TypeCheckerFailure (lazy "Case analysys: wrong branch type"));
          let arguments' =
           if not need_dummy then outtype::arguments@[term]
           else outtype::arguments in
          let outtype =
           if need_dummy && arguments = [] then outtype
           else CicReduction.head_beta_reduce (C.Appl arguments')
          in
           outtype,ugraph5
   | C.Fix (i,fl) ->
      let types,kl,ugraph1,len =
        List.fold_left
          (fun (types,kl,ugraph,len) (n,k,ty,_) ->
            let _,ugraph1 = type_of_aux ~logger context ty ugraph in
             (Some (C.Name n,(C.Decl (CicSubstitution.lift len ty)))::types,
              k::kl,ugraph1,len+1)
          ) ([],[],ugraph,0) fl
      in
      let ugraph2 = 
        List.fold_left
          (fun ugraph (name,x,ty,bo) ->
             let ty_bo,ugraph1 = 
               type_of_aux ~logger (types@context) bo ugraph 
             in
             let b,ugraph2 = 
               R.are_convertible ~subst ~metasenv (types@context) 
                 ty_bo (CicSubstitution.lift len ty) ugraph1 in
               if b then
                 begin
                   let (m, eaten, context') =
                     eat_lambdas ~subst (types @ context) (x + 1) bo
                   in
                   let rec_uri, rec_uri_len =
                    let he =
                     match List.hd context' with
                        Some (_,Cic.Decl he) -> he
                      | _ -> assert false
                    in
                     match CicReduction.whd ~subst (List.tl context') he with
                     | Cic.MutInd (uri,_,_)
                     | Cic.Appl (Cic.MutInd (uri,_,_)::_) ->
                         uri,
                           (match
                            CicEnvironment.get_obj
                             CicUniv.oblivion_ugraph uri
                           with
                           | Cic.InductiveDefinition (tl,_,_,_), _ ->
                               List.length tl
                           | _ -> assert false)
                     | _ -> assert false
                   in 
                     (*
                       let's control the guarded by 
                       destructors conditions D{f,k,x,M}
                     *)
                     if not (guarded_by_destructors ~logger ~metasenv ~subst 
                       rec_uri rec_uri_len context' eaten (len + eaten) kl 
                       1 [] m) 
                     then
                       raise
                         (TypeCheckerFailure 
                           (lazy ("Fix: not guarded by destructors:"^CicPp.ppterm t)))
                     else
                       ugraph2
                 end
               else
                 raise (TypeCheckerFailure (lazy ("Fix: ill-typed bodies")))
          ) ugraph1 fl in
        (*CSC: controlli mancanti solo su D{f,k,x,M} *)
      let (_,_,ty,_) = List.nth fl i in
        ty,ugraph2
   | C.CoFix (i,fl) ->
       let types,ugraph1,len =
         List.fold_left
           (fun (l,ugraph,len) (n,ty,_) -> 
              let _,ugraph1 = 
                type_of_aux ~logger context ty ugraph in 
                (Some (C.Name n,(C.Decl (CicSubstitution.lift len ty)))::l,
                 ugraph1,len+1)
           ) ([],ugraph,0) fl
       in
       let ugraph2 = 
         List.fold_left
           (fun ugraph (_,ty,bo) ->
              let ty_bo,ugraph1 = 
                type_of_aux ~logger (types @ context) bo ugraph 
              in
              let b,ugraph2 = 
                R.are_convertible ~subst ~metasenv (types @ context) ty_bo
                  (CicSubstitution.lift len ty) ugraph1 
              in
                if b then
                  begin
                    (* let's control that the returned type is coinductive *)
                    match returns_a_coinductive ~subst context ty with
                        None ->
                          raise
                          (TypeCheckerFailure
                            (lazy "CoFix: does not return a coinductive type"))
                      | Some uri ->
                          (*
                            let's control the guarded by constructors 
                            conditions C{f,M}
                          *)
                          if not (guarded_by_constructors ~logger ~subst ~metasenv uri
                 (types @ context) 0 len false bo) then
                            raise
                              (TypeCheckerFailure 
                                (lazy "CoFix: not guarded by constructors"))
                          else
                          ugraph2
                  end
                else
                  raise
                    (TypeCheckerFailure (lazy "CoFix: ill-typed bodies"))
           ) ugraph1 fl 
       in
       let (_,ty,_) = List.nth fl i in
         ty,ugraph2

 and check_exp_named_subst uri ~logger ~subst context ens ugraph =
   let params =
    let obj,_ = CicEnvironment.get_obj CicUniv.empty_ugraph uri in
    (match obj with
        Cic.Constant (_,_,_,params,_) -> params
      | Cic.Variable (_,_,_,params,_) -> params
      | Cic.CurrentProof (_,_,_,_,params,_) -> params
      | Cic.InductiveDefinition (_,params,_,_) -> params
    ) in
   let rec check_same_order params ens =
    match params,ens with
     | _,[] -> ()
     | [],_::_ ->
        raise (TypeCheckerFailure (lazy "Bad explicit named substitution"))
     | uri::tl,(uri',_)::tl' when UriManager.eq uri uri' ->
        check_same_order tl tl'
     | _::tl,l -> check_same_order tl l
   in
   let rec check_exp_named_subst_aux ~logger esubsts l ugraph =
     match l with
         [] -> ugraph
       | ((uri,t) as item)::tl ->
           let ty_uri,ugraph1 = type_of_variable ~logger uri ugraph in 
           let typeofvar =
             CicSubstitution.subst_vars esubsts ty_uri in
           let typeoft,ugraph2 = type_of_aux ~logger context t ugraph1 in
           let b,ugraph3 =
             CicReduction.are_convertible ~subst ~metasenv
               context typeoft typeofvar ugraph2 
           in
             if b then
               check_exp_named_subst_aux ~logger (esubsts@[item]) tl ugraph3
             else
               begin
                 CicReduction.fdebug := 0 ;
                 ignore 
                   (CicReduction.are_convertible 
                      ~subst ~metasenv context typeoft typeofvar ugraph2) ;
                 fdebug := 0 ;
                 debug typeoft [typeofvar] ;
                 raise (TypeCheckerFailure (lazy "Wrong Explicit Named Substitution"))
               end
   in
    check_same_order params ens ;
    check_exp_named_subst_aux ~logger [] ens ugraph
       
 and sort_of_prod ~subst context (name,s) (t1, t2) ugraph =
  let module C = Cic in
   let t1' = CicReduction.whd ~subst context t1 in
   let t2' = CicReduction.whd ~subst ((Some (name,C.Decl s))::context) t2 in
   match (t1', t2') with
    | (C.Sort s1, C.Sort (C.Prop | C.Set)) ->
         (* different from Coq manual!!! *)
         t2',ugraph
    | (C.Sort (C.Type t1 | C.CProp t1), C.Sort (C.Type t2)) -> 
       let t' = CicUniv.fresh() in
        (try
         let ugraph1 = CicUniv.add_ge t' t1 ugraph in
         let ugraph2 = CicUniv.add_ge t' t2 ugraph1 in
          C.Sort (C.Type t'),ugraph2
        with
         CicUniv.UniverseInconsistency msg -> raise (TypeCheckerFailure msg))
    | (C.Sort (C.CProp t1 | C.Type t1), C.Sort (C.CProp t2)) -> 
       let t' = CicUniv.fresh() in
        (try
         let ugraph1 = CicUniv.add_ge t' t1 ugraph in
         let ugraph2 = CicUniv.add_ge t' t2 ugraph1 in
          C.Sort (C.CProp t'),ugraph2
        with
         CicUniv.UniverseInconsistency msg -> raise (TypeCheckerFailure msg))
    | (C.Sort _,C.Sort (C.Type t1)) -> C.Sort (C.Type t1),ugraph 
    | (C.Sort _,C.Sort (C.CProp t1)) -> C.Sort (C.CProp t1),ugraph 
    | (C.Meta _, C.Sort _) -> t2',ugraph
    | (C.Meta _, (C.Meta (_,_) as t))
    | (C.Sort _, (C.Meta (_,_) as t)) when CicUtil.is_closed t ->
        t2',ugraph
    | (_,_) -> raise (TypeCheckerFailure (lazy (sprintf
        "Prod: expected two sorts, found = %s, %s" (CicPp.ppterm t1')
          (CicPp.ppterm t2'))))

 and eat_prods ~subst context hetype l ugraph =
   (*CSC: siamo sicuri che le are_convertible non lavorino con termini non *)
   (*CSC: cucinati                                                         *)
   match l with
       [] -> hetype,ugraph
     | (hete, hety)::tl ->
         (match (CicReduction.whd ~subst context hetype) with 
              Cic.Prod (n,s,t) ->
                let b,ugraph1 = 
(*if (match hety,s with Cic.Sort _,Cic.Sort _ -> false | _,_ -> true) && hety <> s then(
prerr_endline ("AAA22: " ^ CicPp.ppterm hete ^ ": " ^ CicPp.ppterm hety ^ " <==> " ^ CicPp.ppterm s); let res = CicReduction.are_convertible ~subst ~metasenv context hety s ugraph in prerr_endline "#"; res) else*)
                  CicReduction.are_convertible 
                    ~subst ~metasenv context hety s ugraph 
                in        
                  if b then
                    begin
                      CicReduction.fdebug := -1 ;
                      eat_prods ~subst context 
                        (CicSubstitution.subst ~avoid_beta_redexes:true hete t)
                         tl ugraph1
                        (*TASSI: not sure *)
                    end
                  else
                    begin
                      CicReduction.fdebug := 0 ;
                      ignore (CicReduction.are_convertible 
                                ~subst ~metasenv context s hety ugraph) ;
                      fdebug := 0 ;
                      debug s [hety] ;
                      raise 
                        (TypeCheckerFailure 
                          (lazy (sprintf
                              ("Appl: wrong parameter-type, expected %s, found %s")
                              (CicPp.ppterm hetype) (CicPp.ppterm s))))
                    end
            | _ ->
                raise (TypeCheckerFailure
                        (lazy "Appl: this is not a function, it cannot be applied"))
         )

 and returns_a_coinductive ~subst context ty =
  let module C = Cic in
   match CicReduction.whd ~subst context ty with
      C.MutInd (uri,i,_) ->
       (*CSC: definire una funzioncina per questo codice sempre replicato *)
        let obj,_ =
          try
            CicEnvironment.get_cooked_obj ~trust:false CicUniv.empty_ugraph uri
          with Not_found -> assert false
        in
        (match obj with
           C.InductiveDefinition (itl,_,_,_) ->
            let (_,is_inductive,_,_) = List.nth itl i in
             if is_inductive then None else (Some uri)
         | _ ->
            raise (TypeCheckerFailure
              (lazy ("Unknown mutual inductive definition:" ^
              UriManager.string_of_uri uri)))
        )
    | C.Appl ((C.MutInd (uri,i,_))::_) ->
       (let o,_ = CicEnvironment.get_obj CicUniv.empty_ugraph uri in
         match o with
           C.InductiveDefinition (itl,_,_,_) ->
            let (_,is_inductive,_,_) = List.nth itl i in
             if is_inductive then None else (Some uri)
         | _ ->
            raise (TypeCheckerFailure
              (lazy ("Unknown mutual inductive definition:" ^
              UriManager.string_of_uri uri)))
        )
    | C.Prod (n,so,de) ->
       returns_a_coinductive ~subst ((Some (n,C.Decl so))::context) de
    | _ -> None

 in
(*CSC
debug_print (lazy ("INIZIO TYPE_OF_AUX " ^ CicPp.ppterm t)) ; flush stderr ;
let res =
*)
  type_of_aux ~logger context t ugraph
(*
in debug_print (lazy "FINE TYPE_OF_AUX") ; flush stderr ; res
*)

(* is a small constructor? *)
(*CSC: ottimizzare calcolando staticamente *)
and is_small_or_non_informative ~condition ~logger context paramsno c ugraph =
 let rec is_small_or_non_informative_aux ~logger context c ugraph =
  let module C = Cic in
   match CicReduction.whd context c with
      C.Prod (n,so,de) ->
       let s,ugraph1 = type_of_aux' ~logger [] context so ugraph in
       let b = condition s in
       if b then
         is_small_or_non_informative_aux
          ~logger ((Some (n,(C.Decl so)))::context) de ugraph1
       else 
                false,ugraph1
    | _ -> true,ugraph (*CSC: we trust the type-checker *)
 in
  let (context',dx) = split_prods ~subst:[] context paramsno c in
   is_small_or_non_informative_aux ~logger context' dx ugraph

and is_small ~logger =
 is_small_or_non_informative
  ~condition:(fun s -> s=Cic.Sort Cic.Prop || s=Cic.Sort Cic.Set)
  ~logger

and is_non_informative ~logger =
 is_small_or_non_informative
  ~condition:(fun s -> s=Cic.Sort Cic.Prop)
  ~logger

and type_of ~logger t ugraph =
(*CSC
debug_print (lazy ("INIZIO TYPE_OF_AUX' " ^ CicPp.ppterm t)) ; flush stderr ;
let res =
*)
 type_of_aux' ~logger [] [] t ugraph 
(*CSC
in debug_print (lazy "FINE TYPE_OF_AUX'") ; flush stderr ; res
*)
;;

let typecheck_obj0 ~logger uri (obj,unchecked_ugraph) =
 let module C = Cic in
 let ugraph = CicUniv.empty_ugraph in
 let inferred_ugraph =
   match obj with
    | C.Constant (_,Some te,ty,_,_) ->
        let _,ugraph = type_of ~logger ty ugraph in
        let ty_te,ugraph = type_of ~logger te ugraph in
        let b,ugraph = (CicReduction.are_convertible [] ty_te ty ugraph) in
         if not b then
           raise (TypeCheckerFailure
            (lazy
              ("the type of the body is not the one expected:\n" ^
               CicPp.ppterm ty_te ^ "\nvs\n" ^
               CicPp.ppterm ty)))
         else
          ugraph
     | C.Constant (_,None,ty,_,_) ->
        (* only to check that ty is well-typed *)
        let _,ugraph = type_of ~logger ty ugraph in
         ugraph
     | C.CurrentProof (_,conjs,te,ty,_,_) ->
        (* this block is broken since the metasenv should 
         * be topologically sorted before typing metas *)
        ignore(assert false);
        let _,ugraph =
         List.fold_left
          (fun (metasenv,ugraph) ((_,context,ty) as conj) ->
            let _,ugraph = 
             type_of_aux' ~logger metasenv context ty ugraph 
            in
             metasenv @ [conj],ugraph
          ) ([],ugraph) conjs
        in
         let _,ugraph = type_of_aux' ~logger conjs [] ty ugraph in
         let type_of_te,ugraph = 
          type_of_aux' ~logger conjs [] te ugraph
         in
         let b,ugraph = CicReduction.are_convertible [] type_of_te ty ugraph in
          if not b then
            raise (TypeCheckerFailure (lazy (sprintf
             "the current proof is not well typed because the type %s of the body is not convertible to the declared type %s"
             (CicPp.ppterm type_of_te) (CicPp.ppterm ty))))
          else
           ugraph
     | C.Variable (_,bo,ty,_,_) ->
        (* only to check that ty is well-typed *)
        let _,ugraph = type_of ~logger ty ugraph in
         (match bo with
             None -> ugraph
           | Some bo ->
              let ty_bo,ugraph = type_of ~logger bo ugraph in
                let b,ugraph = CicReduction.are_convertible [] ty_bo ty ugraph in
               if not b then
                raise (TypeCheckerFailure
                 (lazy "the body is not the one expected"))
               else
                ugraph
              )
     | (C.InductiveDefinition _ as obj) ->
        check_mutual_inductive_defs ~logger uri obj ugraph
 in
   check_and_clean_ugraph inferred_ugraph unchecked_ugraph uri obj
;;

let typecheck ?(trust=true) uri =
 let module C = Cic in
 let module R = CicReduction in
 let module U = UriManager in
 let logger = new CicLogger.logger in
   match CicEnvironment.is_type_checked ~trust CicUniv.empty_ugraph uri with
   | CicEnvironment.CheckedObj (cobj,ugraph') -> cobj,ugraph'
   | CicEnvironment.UncheckedObj (uobj,unchecked_ugraph) ->
      (* let's typecheck the uncooked object *)
      logger#log (`Start_type_checking uri) ;
      let ugraph, ul, obj = typecheck_obj0 ~logger uri (uobj,unchecked_ugraph) in
      CicEnvironment.set_type_checking_info uri (obj,ugraph,ul);
      logger#log (`Type_checking_completed uri);
      match CicEnvironment.is_type_checked ~trust CicUniv.empty_ugraph uri with
      | CicEnvironment.CheckedObj (cobj,ugraph') -> cobj,ugraph'
      | _ -> raise CicEnvironmentError
;;

let typecheck_obj ~logger uri obj =
 let ugraph,univlist,obj = typecheck_obj0 ~logger uri (obj,None) in
 CicEnvironment.add_type_checked_obj uri (obj,ugraph,univlist)

(** wrappers which instantiate fresh loggers *)

let profiler = HExtlib.profile "K/CicTypeChecker.type_of_aux'"

let type_of_aux' ?(subst = []) metasenv context t ugraph =
  let logger = new CicLogger.logger in
  profiler.HExtlib.profile 
    (type_of_aux' ~logger ~subst metasenv context t) ugraph

let typecheck_obj uri obj =
 let logger = new CicLogger.logger in
 typecheck_obj ~logger uri obj

(* check_allowed_sort_elimination uri i s1 s2
   This function is used outside the kernel to determine in advance whether
   a MutCase will be allowed or not.
   [uri,i] is the type of the term to match
   [s1] is the sort of the term to eliminate (i.e. the head of the arity
        of the inductive type [uri,i])
   [s2] is the sort of the goal (i.e. the head of the type of the outtype
        of the MutCase) *)
let check_allowed_sort_elimination uri i s1 s2 =
 fst (check_allowed_sort_elimination ~subst:[] ~metasenv:[]
  ~logger:(new CicLogger.logger) [] uri i true
  (Cic.Implicit None) (* never used *) (Cic.Sort s1) (Cic.Sort s2)
  CicUniv.empty_ugraph)
;;

Deannotate.type_of_aux' :=
 fun context t ->
  ignore (
  List.fold_right
   (fun el context ->
      (match el with
          None -> ()
        | Some (_,Cic.Decl ty) ->
           ignore (type_of_aux' [] context ty CicUniv.empty_ugraph)
        | Some (_,Cic.Def (bo,ty)) ->
           ignore (type_of_aux' [] context ty CicUniv.empty_ugraph);
           ignore (type_of_aux' [] context bo CicUniv.empty_ugraph));
      el::context
   ) context []);
  fst (type_of_aux' [] context t CicUniv.empty_ugraph);;
