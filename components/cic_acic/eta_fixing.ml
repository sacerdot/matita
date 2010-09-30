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

exception ReferenceToNonVariable;;

let prerr_endline _ = ();;

(* 
let rec fix_lambdas_wrt_type ty te =
 let module C = Cic in
 let module S = CicSubstitution in
(*  prerr_endline ("entering fix_lambdas: type=" ^ CicPp.ppterm ty ^ "term=" ^ CicPp.ppterm te); *)
   match ty with
     C.Prod (_,_,ty') ->
       (match CicReduction.whd [] te with
          C.Lambda (n,s,te') ->
            C.Lambda (n,s,fix_lambdas_wrt_type ty' te')
        | t ->
            let rec get_sources =
              function 
                C.Prod (_,s,ty) -> s::(get_sources ty)
              | _ -> [] in
            let sources = get_sources ty in
            let no_sources = List.length sources in
            let rec mk_rels n shift =
              if n = 0 then []
            else (C.Rel (n + shift))::(mk_rels (n - 1) shift) in
            let t' = S.lift no_sources t in
            let t2 = 
              match t' with
                C.Appl l -> 
                  C.LetIn 
                     (C.Name "w",t',C.Appl ((C.Rel 1)::(mk_rels no_sources 1)))
              | _ -> 
                  C.Appl (t'::(mk_rels no_sources 0)) in
                   List.fold_right
                     (fun source t -> C.Lambda (C.Name "y",source,t)) 
                      sources t2)
   | _ -> te
;; *)

let rec fix_lambdas_wrt_type ty te =
 let module C = Cic in
 let module S = CicSubstitution in
(*  prerr_endline ("entering fix_lambdas: type=" ^ CicPp.ppterm ty ^ "term=" ^ CicPp.ppterm te); *)
   match ty,te with
     C.Prod (_,_,ty'), C.Lambda (n,s,te') ->
       C.Lambda (n,s,fix_lambdas_wrt_type ty' te')
   | C.Prod (_,s,ty'), t -> 
      let rec get_sources =
        function 
            C.Prod (_,s,ty) -> s::(get_sources ty)
          | _ -> [] in
      let sources = get_sources ty in
      let no_sources = List.length sources in
      let rec mk_rels n shift =
        if n = 0 then []
        else (C.Rel (n + shift))::(mk_rels (n - 1) shift) in
      let t' = S.lift no_sources t in
      let t2 = 
         match t' with
           C.Appl l -> 
             C.LetIn (C.Name "w",t',assert false,
              C.Appl ((C.Rel 1)::(mk_rels no_sources 1)))
         | _ -> C.Appl (t'::(mk_rels no_sources 0)) in
      List.fold_right
        (fun source t -> C.Lambda (C.Name "y",CicReduction.whd [] source,t)) sources t2
   | _, _ -> te
;;

(*
let rec fix_lambdas_wrt_type ty te =
 let module C = Cic in
 let module S = CicSubstitution in
(*  prerr_endline ("entering fix_lambdas: type=" ^ CicPp.ppterm ty ^ "term=" ^ CicPp.ppterm te); *)
   match ty,te with
     C.Prod (_,_,ty'), C.Lambda (n,s,te') ->
       C.Lambda (n,s,fix_lambdas_wrt_type ty' te')
   | C.Prod (_,s,ty'), ((C.Appl (C.Const _ ::_)) as t) -> 
      (* const have a fixed arity *)
      (* prerr_endline ("******** fl - eta expansion 0: type=" ^ CicPp.ppterm ty ^ "term=" ^ CicPp.ppterm te); *)
       let t' = S.lift 1 t in
       C.Lambda (C.Name "x",s,
         C.LetIn 
          (C.Name "H", fix_lambdas_wrt_type ty' t', 
            C.Appl [C.Rel 1;C.Rel 2])) 
   | C.Prod (_,s,ty'), C.Appl l ->
       (* prerr_endline ("******** fl - eta expansion 1: type=" ^ CicPp.ppterm ty ^ "term=" ^ CicPp.ppterm te); *)
       let l' = List.map (S.lift 1) l in
        C.Lambda (C.Name "x",s,
         fix_lambdas_wrt_type ty' (C.Appl (l'@[C.Rel 1])))
   | C.Prod (_,s,ty'), _ ->
       (* prerr_endline ("******** fl - eta expansion 2: type=" ^ CicPp.ppterm ty ^ "term=" ^ CicPp.ppterm te); *)
       flush stderr ;
       let te' = S.lift 1 te in
        C.Lambda (C.Name "x",s,
          fix_lambdas_wrt_type ty' (C.Appl [te';C.Rel 1]))
   | _, _ -> te
;;*) 

let fix_according_to_type ty hd tl =
 let module C = Cic in
 let module S = CicSubstitution in
   let rec count_prods =
     function
       C.Prod (_,_,t) -> 1 + (count_prods t)
       | _ -> 0 in
  let expected_arity = count_prods ty in
  let rec aux n ty tl res =
    if n = 0 then
      (match tl with 
         [] ->
          (match res with
              [] -> assert false
            | [res] -> res
            | _ -> C.Appl res)
       | _ -> 
          match res with
            [] -> assert false
          | [a] -> C.Appl (a::tl)
          | _ ->
              (* prerr_endline ("******* too many args: type=" ^ CicPp.ppterm ty ^ "term=" ^ CicPp.ppterm (C.Appl res)); *)
              C.LetIn 
                (C.Name "H", 
                  C.Appl res,
                   assert false,
                    C.Appl (C.Rel 1::(List.map (S.lift 1) tl))))
    else 
      let name,source,target =
        (match ty with
           C.Prod (C.Name _ as n,s,t) -> n,s,t
         | C.Prod (C.Anonymous, s,t) -> C.Name "z",s,t
         | _ -> (* prods number may only increase for substitution *) 
           assert false) in
      match tl with 
         [] ->
           (* prerr_endline ("******* too few args: type=" ^ CicPp.ppterm ty ^ "term=" ^ CicPp.ppterm (C.Appl res)); *)
           let res' = List.map (S.lift 1) res in 
           C.Lambda 
            (name, source, aux (n-1) target [] (res'@[C.Rel 1]))
        | hd::tl' -> 
           let hd' = fix_lambdas_wrt_type source hd in
            (*  (prerr_endline ("++++++prima :" ^(CicPp.ppterm hd)); 
              prerr_endline ("++++++dopo :" ^(CicPp.ppterm hd'))); *)
           aux (n-1) (S.subst hd' target) tl' (res@[hd']) in
  aux expected_arity ty tl [hd]
;;

let eta_fix metasenv context t =
 let rec eta_fix' context t = 
  (* prerr_endline ("entering aux with: term=" ^ CicPp.ppterm t); 
  flush stderr ; *)
  let module C = Cic in
  let module S = CicSubstitution in
  match t with
     C.Rel n -> C.Rel n 
   | C.Var (uri,exp_named_subst) ->
      let exp_named_subst' = fix_exp_named_subst context exp_named_subst in
       C.Var (uri,exp_named_subst')
   | C.Meta (n,l) ->
      let (_,canonical_context,_) = CicUtil.lookup_meta n metasenv in
      let l' =
        List.map2
         (fun ct t ->
          match (ct, t) with
            None, _ -> None
          | _, Some t -> Some (eta_fix' context t)
          | Some _, None -> assert false (* due to typing rules *))
        canonical_context l
       in
       C.Meta (n,l')
   | C.Sort s -> C.Sort s
   | C.Implicit _ as t -> t
   | C.Cast (v,t) -> C.Cast (eta_fix' context v, eta_fix' context t)
   | C.Prod (n,s,t) -> 
       C.Prod 
        (n, eta_fix' context s, eta_fix' ((Some (n,(C.Decl s)))::context) t)
   | C.Lambda (n,s,t) -> 
       C.Lambda 
        (n, eta_fix' context s, eta_fix' ((Some (n,(C.Decl s)))::context) t)
   | C.LetIn (n,s,ty,t) -> 
       C.LetIn 
        (n,eta_fix' context s,eta_fix' context ty,
          eta_fix' ((Some (n,(C.Def (s,ty))))::context) t)
   | C.Appl [] -> assert false 
   | C.Appl (he::tl) -> 
       let tl' =  List.map (eta_fix' context) tl in 
       let ty,_ = 
         CicTypeChecker.type_of_aux' metasenv context he 
           CicUniv.oblivion_ugraph 
       in
       fix_according_to_type ty (eta_fix' context he) tl'
(*
         C.Const(uri,exp_named_subst)::l'' ->
           let constant_type =
             (match CicEnvironment.get_obj uri with
               C.Constant (_,_,ty,_) -> ty
             | C.Variable _ -> raise ReferenceToVariable
             | C.CurrentProof (_,_,_,_,params) -> raise ReferenceToCurrentProof
             | C.InductiveDefinition _ -> raise ReferenceToInductiveDefinition
             ) in 
           fix_according_to_type 
             constant_type (C.Const(uri,exp_named_subst)) l''
        | _ -> C.Appl l' *)
   | C.Const (uri,exp_named_subst) ->
       let exp_named_subst' = fix_exp_named_subst context exp_named_subst in
        C.Const (uri,exp_named_subst')
   | C.MutInd (uri,tyno,exp_named_subst) ->
       let exp_named_subst' = fix_exp_named_subst context exp_named_subst in
        C.MutInd (uri, tyno, exp_named_subst')
   | C.MutConstruct (uri,tyno,consno,exp_named_subst) ->
       let exp_named_subst' = fix_exp_named_subst context exp_named_subst in
        C.MutConstruct (uri, tyno, consno, exp_named_subst')
   | C.MutCase (uri, tyno, outty, term, patterns) ->
       let outty' =  eta_fix' context outty in
       let term' = eta_fix' context term in
       let patterns' = List.map (eta_fix' context) patterns in
       let inductive_types,noparams =
	 let o,_ = CicEnvironment.get_obj CicUniv.oblivion_ugraph uri in
           (match o with
               Cic.Constant _ -> assert false
             | Cic.Variable _ -> assert false
             | Cic.CurrentProof _ -> assert false
             | Cic.InductiveDefinition (l,_,n,_) -> l,n 
           ) in
       let (_,_,_,constructors) = List.nth inductive_types tyno in
       let constructor_types = 
         let rec clean_up t =
           function 
               [] -> t
             | a::tl -> 
                 (match t with
                   Cic.Prod (_,_,t') -> clean_up (S.subst a t') tl
                  | _ -> assert false) in
          if noparams = 0 then 
            List.map (fun (_,t) -> t) constructors 
          else 
	    let term_type,_ = 
              CicTypeChecker.type_of_aux' metasenv context term
		CicUniv.oblivion_ugraph 
            in
            (match term_type with
               C.Appl (hd::params) -> 
                 let rec first_n n l =
                   if n = 0 then []
                   else 
                     (match l with
                        a::tl -> a::(first_n (n-1) tl)
		      | _ -> assert false) in 
                 List.map 
                  (fun (_,t) -> 
                     clean_up t (first_n noparams params)) constructors
             | _ -> prerr_endline ("QUA"); assert false) in 
       let patterns2 = 
         List.map2 fix_lambdas_wrt_type
           constructor_types patterns' in 
         C.MutCase (uri, tyno, outty',term',patterns2)
   | C.Fix (funno, funs) ->
       let fun_types = 
         List.map (fun (n,_,ty,_) -> Some (C.Name n,(Cic.Decl ty))) funs in
       C.Fix (funno,
        List.map
         (fun (name, no, ty, bo) ->
           (name, no, eta_fix' context ty, eta_fix' (fun_types@context) bo)) 
        funs)
   | C.CoFix (funno, funs) ->
       let fun_types = 
         List.map (fun (n,ty,_) -> Some (C.Name n,(Cic.Decl ty))) funs in
       C.CoFix (funno,
        List.map
         (fun (name, ty, bo) ->
           (name, eta_fix' context ty, eta_fix' (fun_types@context) bo)) funs)
  and fix_exp_named_subst context exp_named_subst =
   List.rev
    (List.fold_left
      (fun newsubst (uri,t) ->
        let t' = eta_fix' context t in
        let ty =
	  let o,_ = CicEnvironment.get_obj CicUniv.oblivion_ugraph uri in
            match o with
		Cic.Variable (_,_,ty,_,_) -> 
		  CicSubstitution.subst_vars newsubst ty
              | _ ->  raise ReferenceToNonVariable 
	in
        let t'' = fix_according_to_type ty t' [] in
         (uri,t'')::newsubst
      ) [] exp_named_subst)
  in
   eta_fix' context t
;;
