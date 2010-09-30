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

module C = Cic
module U = UriManager
module P = PrimitiveTactics
module T = Tacticals
module CR = CicReduction 
module PST = ProofEngineStructuralRules
module PET = ProofEngineTypes
module CTC = CicTypeChecker
module CU = CicUniv
module S = CicSubstitution
module RT = ReductionTactics
module PEH = ProofEngineHelpers
module ET = EqualityTactics
module DTI = DoubleTypeInference

let debug = false
let debug_print = 
  if debug then (fun x -> prerr_endline (Lazy.force x)) else (fun _ -> ())

(* term ha tipo t1=t2; funziona solo se t1 e t2 hanno in testa costruttori
diversi *)

let discriminate_tac ~term =
 let true_URI =
  match LibraryObjects.true_URI () with
     Some uri -> uri
   | None -> raise (PET.Fail (lazy "You need to register the default \"true\" definition first. Please use the \"default\" command")) in
 let false_URI =
  match LibraryObjects.false_URI () with
     Some uri -> uri
   | None -> raise (PET.Fail (lazy "You need to register the default \"false\" definition first. Please use the \"default\" command")) in
 let fail msg = raise (PET.Fail (lazy ("Discriminate: " ^ msg))) in
 let find_discriminating_consno t1 t2 =
   let rec aux t1 t2 =
     match t1, t2 with
     | C.MutConstruct _, C.MutConstruct _ when t1 = t2 -> None
     | C.Appl ((C.MutConstruct _ as constr1) :: args1),
       C.Appl ((C.MutConstruct _ as constr2) :: args2)
       when constr1 = constr2 ->
         let rec aux_list l1 l2 =
           match l1, l2 with
           | [], [] -> None
           | hd1 :: tl1, hd2 :: tl2 ->
               (match aux hd1 hd2 with
               | None -> aux_list tl1 tl2
               | Some _ as res -> res)
           | _ -> (* same constructor applied to a different number of args *)
               assert false
         in
         aux_list args1 args2
     | ((C.MutConstruct (_,_,consno1,subst1)),
       (C.MutConstruct (_,_,consno2,subst2)))
     | ((C.MutConstruct (_,_,consno1,subst1)),
       (C.Appl ((C.MutConstruct (_,_,consno2,subst2)) :: _)))
     | ((C.Appl ((C.MutConstruct (_,_,consno1,subst1)) :: _)),
       (C.MutConstruct (_,_,consno2,subst2)))
     | ((C.Appl ((C.MutConstruct (_,_,consno1,subst1)) :: _)),
       (C.Appl ((C.MutConstruct (_,_,consno2,subst2)) :: _)))
       when (consno1 <> consno2) || (subst1 <> subst2) ->
         Some consno2
     | _ -> fail "not a discriminable equality"
   in
   aux t1 t2
 in
 let mk_branches_and_outtype turi typeno consno context args =
    (* a list of "True" except for the element in position consno which
     * is "False" *)
    match fst (CicEnvironment.get_obj CU.oblivion_ugraph turi) with
    | C.InductiveDefinition (ind_type_list,_,paramsno,_)  ->
        let _,_,rty,constructor_list = List.nth ind_type_list typeno in 
        let false_constr_id,_ = List.nth constructor_list (consno - 1) in
        let branches =
         List.map 
           (fun (id,cty) ->
             (* dubbio: e' corretto ridurre in questo context ??? *)
             let red_ty = CR.whd context cty in
             let rec aux t k =
               match t with
               | C.Prod (_,_,target) when (k <= paramsno) ->
                   S.subst (List.nth args (k-1))
                     (aux target (k+1))
               | C.Prod (binder,source,target) when (k > paramsno) ->
                   C.Lambda (binder, source, (aux target (k+1)))
               | _ -> 
                   if (id = false_constr_id)
                   then (C.MutInd(false_URI,0,[]))
                   else (C.MutInd(true_URI,0,[]))
             in
             (S.lift 1 (aux red_ty 1)))
           constructor_list in
        let outtype =
         let seed = ref 0 in
         let rec mk_lambdas rev_left_args =
          function
             0, args, C.Prod (_,so,ta) ->
              C.Lambda
               (C.Name (incr seed; "x" ^ string_of_int !seed),
               so,
               mk_lambdas rev_left_args (0,args,ta))
           | 0, args, C.Sort _ ->
              let rec mk_rels =
               function
                  0 -> []
                | n -> C.Rel n :: mk_rels (n - 1) in
              let argsno = List.length args in
               C.Lambda
                (C.Name "x",
                 (if argsno + List.length rev_left_args > 0 then
                   C.Appl
                    (C.MutInd (turi, typeno, []) ::
                     (List.map
                      (S.lift (argsno + 1))
                      (List.rev rev_left_args)) @
                     mk_rels argsno)
                  else
                   C.MutInd (turi,typeno,[])),
                 C.Sort C.Prop)
           | 0, _, _ -> assert false (* seriously screwed up *)
           | n, he::tl, C.Prod (_,_,ta) ->
              mk_lambdas (he::rev_left_args)(n-1,tl,S.subst he ta)
           | n,_,_ ->
              assert false (* we should probably reduce in some context *)
         in
          mk_lambdas [] (paramsno, args, rty)
        in
         branches, outtype 
    | _ -> assert false
 in
 let discriminate'_tac ~term status = 
  let (proof, goal) = status in
  let _,metasenv,_subst,_,_, _ = proof in
  let _,context,_ = CicUtil.lookup_meta goal metasenv in
  let termty,_ = 
    CTC.type_of_aux' metasenv context term CU.oblivion_ugraph
  in
  match termty with
   | C.Appl [(C.MutInd (equri, 0, [])) ; tty ; t1 ; t2]
     when LibraryObjects.is_eq_URI equri ->
      let turi,typeno,exp_named_subst,args = 
        match tty with
        | (C.MutInd (turi,typeno,exp_named_subst)) ->
            turi,typeno,exp_named_subst,[]
        | (C.Appl (C.MutInd (turi,typeno,exp_named_subst)::args)) ->
            turi,typeno,exp_named_subst,args
        | _ -> fail "not a discriminable equality"
      in
      let consno =
        match find_discriminating_consno t1 t2 with
        | Some consno -> consno
        | None -> fail "discriminating terms are structurally equal"
      in
      let branches,outtype =
       mk_branches_and_outtype turi typeno consno context args
      in
      PET.apply_tactic
       (T.then_
         ~start:(EliminationTactics.elim_type_tac (C.MutInd (false_URI, 0, [])))
         ~continuation:
           (T.then_
             ~start:
               (RT.change_tac 
                 ~pattern:(PET.conclusion_pattern None)
                 (fun _ m u ->
                   C.Appl [
                     C.Lambda ( C.Name "x", tty,
                       C.MutCase (turi, typeno, outtype, (C.Rel 1), branches));
                     t2 ],
                   m, u))
             ~continuation:
               (T.then_
                 ~start:
                   (ET.rewrite_simpl_tac
                     ~direction:`RightToLeft
                     ~pattern:(PET.conclusion_pattern None)
                     term [])
                 ~continuation:
                   (IntroductionTactics.constructor_tac ~n:1)))) status
    | _ -> fail "not an equality"
  in
  PET.mk_tactic (discriminate'_tac ~term)

let exn_noneq = 
  PET.Fail (lazy "Injection: not an equality")
let exn_nothingtodo = 
  PET.Fail (lazy "Nothing to do")
let exn_discrnonind =
  PET.Fail (lazy "Discriminate: object is not an Inductive Definition: it's imposible")
let exn_injwronggoal = 
  PET.Fail (lazy "Injection: goal after cut is not correct")
let exn_noneqind =
  PET.Fail (lazy "Injection: not an equality over elements of an inductive type")

let pp ctx t = 
  let names = List.map (function Some (n,_) -> Some n | None -> None) ctx in
  CicPp.pp t names

let clear_term first_time lterm =
   let clear_term status =
      let (proof, goal) = status in
      let _,metasenv,_subst,_,_, _ = proof in
      let _,context,_ = CicUtil.lookup_meta goal metasenv in
      let term, metasenv, _ugraph = lterm context metasenv CU.oblivion_ugraph in
      debug_print (lazy ("\nclear di: " ^ pp context term));
      debug_print (lazy ("nel contesto:\n" ^ CicPp.ppcontext context)); 
      let g () = if first_time then raise exn_nothingtodo else T.id_tac in
      let tactic = match term with
         | C.Rel n -> 
	    begin match List.nth context (pred n) with
               | Some (C.Name id, _) -> 
	          T.if_ ~fail:(g ()) ~start:(PST.clear ~hyps:[id]) ~continuation:T.id_tac
	       | _ -> assert false
            end
          | _      -> g ()
      in
      PET.apply_tactic tactic status
   in
   PET.mk_tactic clear_term

let exists context = function
   | C.Rel i -> List.nth context (pred i) <> None
   | _       -> true

let recur_on_child_tac ~before ~after =
   let recur_on_child status = 
      let (proof, goal) = status in
      let _, metasenv, _subst, _, _, _ = proof in
      let _, context, _ = CicUtil.lookup_meta goal metasenv in
      debug_print (lazy ("\nrecur_on_child"));
      debug_print (lazy ("nel contesto:\n" ^ CicPp.ppcontext context));      
      let mk_lterm term c m ug =
         let distance = List.length c - List.length context in
         S.lift distance term, m, ug
      in
      let lterm = mk_lterm (Cic.Rel 1) in
      let tactic = T.then_ ~start:before ~continuation:(after lterm) in
      PET.apply_tactic tactic status  
   in
   PET.mk_tactic recur_on_child
   
let injection_tac ~lterm ~i ~continuation ~recur =
 let give_name seed = function
   | C.Name _ as name -> name
   | C.Anonymous -> C.Name (incr seed; "y" ^ string_of_int !seed)
 in
 let rec mk_rels = function | 0 -> [] | n -> C.Rel n :: (mk_rels (n - 1)) in
 let injection_tac status =
  let (proof, goal) = status in
  (* precondizione: t1 e t2 hanno in testa lo stesso costruttore ma 
   * differiscono (o potrebbero differire?) nell'i-esimo parametro 
   * del costruttore *)
  let _,metasenv,_subst,_,_, _ = proof in
  let _,context,_ = CicUtil.lookup_meta goal metasenv in
  let term, metasenv, _ugraph = lterm context metasenv CU.oblivion_ugraph in
  let termty,_ =
    CTC.type_of_aux' metasenv context term CU.oblivion_ugraph
  in
  debug_print (lazy ("\ninjection su : " ^ pp context termty)); 
  match termty with (* an equality *)
   | C.Appl [(C.MutInd (equri, 0, [])) ; tty ; t1 ; t2]
    when LibraryObjects.is_eq_URI equri -> 
      let turi,typeno,ens,params =
        match tty with (* some inductive type *)
        | C.MutInd (turi,typeno,ens) -> turi,typeno,ens,[]
        | C.Appl (C.MutInd (turi,typeno,ens)::params) -> turi,typeno,ens,params
        | _ -> raise exn_noneqind
      in
      let t1',t2',consno = (* sono i due sottotermini che differiscono *)
        match t1,t2 with
        | C.Appl ((C.MutConstruct (uri1,typeno1,consno1,ens1))::applist1),
          C.Appl ((C.MutConstruct (uri2,typeno2,consno2,ens2))::applist2)
          when (uri1 = uri2) && (typeno1 = typeno2) && 
               (consno1 = consno2) && (ens1 = ens2) -> 
               (* controllo ridondante *)
            List.nth applist1 (pred i),List.nth applist2 (pred i),consno2
        | _ -> assert false
      in
      let tty',_ = CTC.type_of_aux' metasenv context t1' CU.oblivion_ugraph in
      let patterns,outtype =
        match fst (CicEnvironment.get_obj CU.oblivion_ugraph turi) with
        | C.InductiveDefinition (ind_type_list,_,paramsno,_)->
           let left_params, right_params = HExtlib.split_nth paramsno params in
           let _,_,_,constructor_list = List.nth ind_type_list typeno in
           let i_constr_id,_ = List.nth constructor_list (consno - 1) in
           let patterns =
             let seed = ref 0 in
             List.map
               (function (id,cty) ->
                 let reduced_cty = CR.whd context cty in
                 let rec aux k = function
                   | C.Prod (_,_,tgt) when k <= paramsno -> 
                       let left = List.nth left_params (k-1) in
                       aux (k+1) (S.subst left tgt)
                   | C.Prod (binder,source,target) when k > paramsno ->
                      let binder' = give_name seed binder in
                      C.Lambda (binder',source,(aux (k+1) target))
                   | _ ->
                     let nr_param_constr = k - paramsno - 1 in
                     if id = i_constr_id then C.Rel (k - i)
                     else S.lift nr_param_constr t1' 
                     (* + 1 per liftare anche il lambda aggiunto
                      * esternamente al case *)
                 in S.lift 1 (aux 1 reduced_cty))
               constructor_list 
           in
           (* this code should be taken from cases_tac *)
           let outtype =
             let seed = ref 0 in
             let rec to_lambdas te head =
               match CR.whd context te with
               | C.Prod (binder,so,ta) ->
                   let binder' = give_name seed binder in
                   C.Lambda (binder',so,to_lambdas ta head)
               | _ -> head 
             in
             let rec skip_prods params te =
               match params, CR.whd context te with
               | [], _ -> te
               | left::tl, C.Prod (_,_,ta) -> 
                   skip_prods tl (S.subst left ta)
               | _, _ -> assert false
             in
             let abstracted_tty =
               let tty =
                 List.fold_left (fun x y -> S.subst y x) tty left_params
               in
               (* non lift, ma subst coi left! *)
               match S.lift 1 tty with
               | C.MutInd _ as tty' -> tty'
               | C.Appl l ->
                   let keep,abstract = HExtlib.split_nth (paramsno +1) l in
                   let keep = List.map (S.lift paramsno) keep in
                   C.Appl (keep@mk_rels (List.length abstract))
               | _ -> assert false
             in
             match ind_type_list with
             | [] -> assert false
             | (_,_,ty,_)::_ ->
               (* this is in general wrong, do as in cases_tac *)
               to_lambdas (skip_prods left_params ty)
                 (C.Lambda 
                   (C.Name "cased", abstracted_tty,
                     (* here we should capture right parameters *)
                     (* 1 for his Lambda, one for the Lambda outside the match
                      * and then one for each to_lambda *)
                     S.lift (2+List.length right_params) tty'))
          in
            patterns,outtype
        | _ -> raise exn_discrnonind
      in
      let cutted = C.Appl [C.MutInd (equri,0,[]) ; tty' ; t1' ; t2'] in
      let changed = 
        C.Appl [ C.Lambda (C.Name "x", tty, 
                  C.MutCase (turi,typeno,outtype,C.Rel 1,patterns)) ; t1]
      in
      (* check if cutted and changed are well typed and if t1' ~ changed *)
      let go_on =
        try
          let _,g = CTC.type_of_aux' metasenv context  cutted
            CU.oblivion_ugraph
          in
          let _,g = CTC.type_of_aux' metasenv context changed g in
          fst (CR.are_convertible ~metasenv context  t1' changed g)
        with
        | CTC.TypeCheckerFailure _ -> false
      in
      if not go_on then begin
        HLog.warn "destruct: injection failed";
        PET.apply_tactic continuation status
      end else
        let fill_cut_tac term = 
	   let fill_cut status =
               debug_print (lazy "riempio il cut"); 
               let (proof, goal) = status in
               let _,metasenv,_subst,_,_, _ = proof in
               let _,context,gty = CicUtil.lookup_meta goal metasenv in
               let gty = Unshare.unshare gty in
               let new_t1' = match gty with 
                  | (C.Appl (C.MutInd (_,_,_)::_::t::_)) -> t
                  | _ -> raise exn_injwronggoal
               in
               debug_print (lazy ("metto: " ^ pp context changed));
               debug_print (lazy ("al posto di: " ^ pp context new_t1'));
               debug_print (lazy ("nel goal: " ^ pp context gty));
               debug_print (lazy ("nel contesto:\n" ^ CicPp.ppcontext context));
               debug_print (lazy ("e poi rewrite con: "^pp context term));
               let tac = T.seq ~tactics:[
	          RT.change_tac
                     ~pattern:(None, [], Some (PEH.pattern_of ~term:gty [new_t1']))
                     (fun _ m u -> changed,m,u);
		  ET.rewrite_simpl_tac
                     ~direction:`LeftToRight
                     ~pattern:(PET.conclusion_pattern None)
                     term [];
                  ET.reflexivity_tac   
	       ] in
	       PET.apply_tactic tac status
	   in
	   PET.mk_tactic fill_cut
	in
	debug_print (lazy ("CUT: " ^ pp context cutted));  
	let tactic = 
	   T.thens ~start: (P.cut_tac cutted)
                   ~continuations:[
	              recur_on_child_tac continuation recur;
		      fill_cut_tac term
	           ]
        in
	PET.apply_tactic tactic status
   | _ -> raise exn_noneq
 in
  PET.mk_tactic injection_tac

let subst_tac ~lterm ~direction ~where ~continuation ~recur =
   let subst_tac status =
      let (proof, goal) = status in
      let _,metasenv,_subst,_,_, _ = proof in
      let _,context,_ = CicUtil.lookup_meta goal metasenv in
      let term, metasenv, _ugraph = lterm context metasenv CU.oblivion_ugraph in
      debug_print (lazy ("\nsubst " ^ (match direction with `LeftToRight -> "->" | `RightToLeft -> "<-") ^ " di: " ^ pp context term));
      let tactic = match where with
         | None      -> 
	    debug_print (lazy ("nella conclusione"));
	    let pattern = PET.conclusion_pattern None in
            let tactic = ET.rewrite_tac ~direction ~pattern term [] in
            T.then_ ~start:(T.try_tactic ~tactic) ~continuation
	 | Some name ->
            debug_print (lazy ("nella premessa: " ^ name));
	    let pattern = None, [name, PET.hole], None in
            let start = ET.rewrite_tac ~direction ~pattern term [] in
            let ok_tactic = recur_on_child_tac continuation recur in
	    T.if_ ~start ~continuation:ok_tactic ~fail:continuation	    
      in 
      PET.apply_tactic tactic status
   in
   PET.mk_tactic subst_tac

let rec destruct ~first_time lterm =
 let are_convertible hd1 hd2 metasenv context = 
   fst (CR.are_convertible ~metasenv context hd1 hd2 CU.oblivion_ugraph)
 in
 let recur = destruct ~first_time:false in
 let destruct status = 
  let (proof, goal) = status in
  let _,metasenv,_subst, _,_, _ = proof in
  let _,context,_ = CicUtil.lookup_meta goal metasenv in
  let term, metasenv, _ugraph = lterm context metasenv CU.oblivion_ugraph in
  let tactic = if not (first_time || exists context term) then T.id_tac else begin
     debug_print (lazy ("\ndestruct di: " ^ pp context term)); 
     debug_print (lazy ("nel contesto:\n" ^ CicPp.ppcontext context));
     let termty,_ = CTC.type_of_aux' metasenv context term CU.oblivion_ugraph in
     debug_print (lazy ("\ndestruct su: " ^ pp context termty)); 
     let mk_lterm term c m ug =
        let distance = List.length c - List.length context in
        S.lift distance term, m, ug
     in
     let lterm = mk_lterm term in
     let mk_subst_chain direction index with_what what =
        let k = match term with C.Rel i -> i | _ -> -1 in
        let rec traverse_context first_time j = function
           | [] ->	   
	      let continuation =
	         T.seq ~tactics:[
	            clear_term first_time lterm;
		    clear_term false (mk_lterm what);
		    clear_term false (mk_lterm with_what)
	         ]
	      in
	      subst_tac ~direction ~lterm ~where:None ~continuation ~recur
           | Some (C.Name name, _) :: tl when j < index && j <> k ->
	      debug_print (lazy ("\nsubst programmata: cosa: " ^ string_of_int index ^ ", dove: " ^ string_of_int j));
	      subst_tac ~direction ~lterm ~where:(Some name) ~recur 
	                ~continuation:(traverse_context false (succ j) tl)
           | _ :: tl -> traverse_context first_time (succ j) tl
        in
        traverse_context first_time 1 context
     in
     match termty with
    | C.Appl [(C.MutInd (equri, 0, [])) ; tty ; t1 ; t2] 
      when LibraryObjects.is_eq_URI equri ->
          begin match t1,t2 with
(* injection part *)
	    | C.MutConstruct _,
              C.MutConstruct _
              when t1 = t2 -> clear_term first_time lterm
            | C.Appl (C.MutConstruct _ as mc1 :: applist1),
              C.Appl (C.MutConstruct _ as mc2 :: applist2)
              when mc1 = mc2 ->
                let rec traverse_list first_time i l1 l2 = 
		   match l1, l2 with
                      | [], [] -> clear_term first_time lterm
                      | hd1 :: tl1, hd2 :: tl2 -> 
                        if are_convertible hd1 hd2 metasenv context then
                           traverse_list first_time (succ i) tl1 tl2
                        else
			   injection_tac ~i ~lterm ~recur ~continuation:
		              (traverse_list false (succ i) tl1 tl2)
                      | _ -> assert false 
                      (* i 2 termini hanno in testa lo stesso costruttore, 
                       * ma applicato a un numero diverso di termini *)
                in
                  traverse_list first_time 1 applist1 applist2
(* discriminate part *)
	    | C.MutConstruct (_,_,consno1,ens1),
              C.MutConstruct (_,_,consno2,ens2)
            | C.MutConstruct (_,_,consno1,ens1),
              C.Appl ((C.MutConstruct (_,_,consno2,ens2))::_)
            | C.Appl ((C.MutConstruct (_,_,consno1,ens1))::_),
              C.MutConstruct (_,_,consno2,ens2)
            | C.Appl ((C.MutConstruct (_,_,consno1,ens1))::_),
              C.Appl ((C.MutConstruct (_,_,consno2,ens2))::_)
              when (consno1 <> consno2) || (ens1 <> ens2) -> 
                discriminate_tac ~term
(* subst part *)
            | C.Rel _, C.Rel _ when t1 = t2 ->
		T.seq ~tactics:[
		   clear_term first_time lterm;
		   clear_term false (mk_lterm t1)
		]
	    | C.Rel i1, C.Rel i2 when i1 < i2 ->  
	       mk_subst_chain `LeftToRight i1 t2 t1
	    | C.Rel i1, C.Rel i2 when i1 > i2 ->
	       mk_subst_chain `RightToLeft i2 t1 t2
	    | C.Rel i1, _ when DTI.does_not_occur i1 t2 ->
	       mk_subst_chain `LeftToRight i1 t2 t1
	    | _, C.Rel i2 when DTI.does_not_occur i2 t1 ->
	       mk_subst_chain `RightToLeft i2 t1 t2
(* else part *)
	    | _ when first_time -> raise exn_nothingtodo
	    | _ (* when not first time *) -> T.id_tac
           end
     | _ when first_time -> raise exn_nothingtodo
     | _ (* when not first time *) -> T.id_tac
  end in  
    PET.apply_tactic tactic status
 in 
   PET.mk_tactic destruct

(* destruct performs either injection or discriminate or subst *)
let destruct_tac xterms =
   let destruct status =
      let (proof, goal) = status in
      let _,metasenv,_subst,_,_, _ = proof in
      let _,context,_ = CicUtil.lookup_meta goal metasenv in
      let mk_lterm term c m ug =
         let distance = List.length c - List.length context in
          S.lift distance term, m, ug
      in
      let tactics = match xterms with 
         | Some terms -> 
	    let map term = destruct ~first_time:false (mk_lterm term) in
	    List.map map terms
         | None       ->
            let rec mk_tactics first_time i tacs = function
	       | []           -> List.rev tacs
	       | Some _ :: tl -> 
	          let lterm = mk_lterm (C.Rel i) in
	          let tacs = destruct ~first_time lterm :: tacs in
	          mk_tactics false (succ i) tacs tl 
	       | _ :: tl      -> mk_tactics first_time (succ i) tacs tl
	    in
	    mk_tactics false 1 [] context
      in
      PET.apply_tactic (T.seq ~tactics) status
   in
   PET.mk_tactic destruct
