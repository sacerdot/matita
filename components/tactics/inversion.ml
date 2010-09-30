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

let debug = false;; 
let debug_print =
 fun msg -> if debug then prerr_endline (Lazy.force msg) else ()


let inside_obj = function
 | Cic.InductiveDefinition (type_list,params, nleft, _) ->
  (type_list,params,nleft)
 | _ -> raise (Invalid_argument "Errore in inside_obj")

let term_to_list = function
 | Cic.Appl l -> l
 | _ -> raise (Invalid_argument "Errore in term_to_list")


let rec baseuri_of_term = function
 | Cic.Appl l -> baseuri_of_term (List.hd l)  
 | Cic.MutInd (baseuri, tyno, []) -> baseuri
 | _ -> raise (Invalid_argument "baseuri_of_term")

(* returns DX1 = DX1 -> ... DXn=DXn -> GOALTY *)
let rec foo_cut nleft parameters parameters_ty body uri_of_eq selections = 
 if nleft > 0 
 then 
  foo_cut (nleft-1) (List.tl parameters)  (List.tl parameters_ty) body 
   uri_of_eq selections
 else
  match parameters,selections with
   | hd::tl, x::xs when x -> 
    Cic.Prod (
     Cic.Anonymous, 
     Cic.Appl[Cic.MutInd (uri_of_eq  ,0,[]);
      (List.hd parameters_ty) ; hd; hd], 
     foo_cut nleft (List.map (CicSubstitution.lift 1) tl) 
      (List.map (CicSubstitution.lift 1) (List.tl parameters_ty)) 
      (CicSubstitution.lift 1 body) uri_of_eq xs)
   | hd::tl,x::xs ->
      foo_cut nleft tl (List.tl parameters_ty) body uri_of_eq xs
   | [],[] -> body
   | _ -> raise (Invalid_argument "inverter: the selection doesn't match the arity of the specified inductive type")
;;

(* from a complex Cic.Prod term, return the list of its components *)
let rec get_sort_type term =
 match term with 
  | Cic.Prod (_,src,tgt) -> (get_sort_type tgt)
  | _ -> term
;;


let rec cut_first n l =
 if n>0 then  
  match l with
   | hd::tl -> cut_first (n-1) tl
   | [] -> []
 else l
;;


let rec cut_last l =
 match l with
  | hd::tl when tl != [] -> hd:: (cut_last tl)
  | _ -> []
;;

(* returns the term to apply*)
let foo_appl nleft nright_consno term uri =
 let l = [] in
 let a = ref l in
 for n = 1 to nleft do
	a := !a @ [(Cic.Implicit None)]
 done;
 a:= !a @ [term];
 for n = 1 to nright_consno do
	a := !a @ [(Cic.Implicit None)] 
 done;
 (*  apply     i_ind           ? ... ?    H *)
 Cic.Appl ([Cic.Const(uri,[])] @ !a @ [Cic.Rel 1])
;;


(* induction/inversion, abbastanza semplicemente, consiste nel generare i prod
 * delle uguaglianze corrispondenti ai soli parametri destri appartenenti all'insieme S.
 * Attenzione al caso base: cos'e` replace_lifting?
 * S = {} e` il principio di induzione
 * S = insieme_dei_destri e` il principio di inversione *)
let rec foo_prod nright right_param_tys rightparameters l2 base_rel goalty 
 uri_of_eq rightparameters_ termty isSetType term selections selections_ =
  match right_param_tys, selections with
   | hd::tl, x::xs when x -> Cic.Prod (
    Cic.Anonymous, 
    Cic.Appl
     [Cic.MutInd(uri_of_eq,0,[]); hd; (List.hd rightparameters); 
     Cic.Rel base_rel],
    foo_prod (nright-1) 
     (List.map (CicSubstitution.lift 1) tl) 
     (List.map (CicSubstitution.lift 1) (List.tl rightparameters)) 
     (List.map (CicSubstitution.lift 1) l2) 
     base_rel (CicSubstitution.lift 1 goalty) uri_of_eq
     (List.map (CicSubstitution.lift 1) rightparameters_) 
     (CicSubstitution.lift 1 termty)
     isSetType (CicSubstitution.lift 1 term)) xs selections_
   | hd::tl, x::xs -> 
       foo_prod (nright-1) tl (List.tl rightparameters) l2 
                        (base_rel-1) goalty uri_of_eq rightparameters_ termty
                        isSetType term xs selections_
   | [],[] -> 
       ProofEngineReduction.replace_lifting 
    ~equality:(fun _ -> CicUtil.alpha_equivalence)
    ~context:[]
    ~what: (if isSetType
     then rightparameters_ @ [term]
     else rightparameters_ ) 
    ~with_what: (List.map (CicSubstitution.lift (-1)) l2)
    ~where:goalty 
   | _ -> raise (Invalid_argument "inverter: the selection doesn't match the arity of the specified inductive type")
(* the same subterm of goalty could be simultaneously sx and dx!*)
;;

(* induction/inversion, abbastanza semplicemente, consiste nel generare i lambda
 * soltanto per i parametri destri appartenenti all'insieme S.
 * Warning: non ne sono piu` cosi` sicuro...
 * S = {} e` il principio di induzione
 * S = insieme_dei_destri e` il principio di inversione *)
let rec foo_lambda nright right_param_tys nright_ right_param_tys_ 
 rightparameters created_vars base_rel goalty uri_of_eq rightparameters_ 
 termty isSetType term selections =
  match right_param_tys with
   | hd::tl -> Cic.Lambda (
    (Cic.Name ("lambda" ^ (string_of_int nright))),
    hd, (* type *)
    foo_lambda (nright-1) 
     (List.map (CicSubstitution.lift 1) tl) nright_ 
     (List.map (CicSubstitution.lift 1) right_param_tys_)
     (List.map (CicSubstitution.lift 1) rightparameters) 
     (List.map (CicSubstitution.lift 1) (created_vars @ [Cic.Rel 1])) 
     base_rel (CicSubstitution.lift 1 goalty) uri_of_eq
     (List.map (CicSubstitution.lift 1) rightparameters_) 
     (CicSubstitution.lift 1 termty) isSetType
     (CicSubstitution.lift 1 term)) selections
   | [] when isSetType -> Cic.Lambda (
    (Cic.Name ("lambda" ^ (string_of_int nright))),
    (ProofEngineReduction.replace_lifting
     ~equality:(fun _ -> CicUtil.alpha_equivalence)
     ~context:[]
     ~what: (rightparameters_ ) 
     ~with_what: (List.map (CicSubstitution.lift (-1)) created_vars)
     ~where:termty), (* type of H with replaced right parameters *)
    foo_prod nright_ (List.map (CicSubstitution.lift 1) right_param_tys_) 
     (List.map (CicSubstitution.lift 1) rightparameters)  
     (List.map (CicSubstitution.lift 1) (created_vars @ [Cic.Rel 1])) 
     (base_rel+1) (CicSubstitution.lift 1 goalty) uri_of_eq
     (List.map (CicSubstitution.lift 1) rightparameters_) 
     (CicSubstitution.lift 1 termty) isSetType
     (CicSubstitution.lift 1 term)) selections selections 
   | [] -> foo_prod nright_ right_param_tys_ rightparameters created_vars 
             base_rel goalty uri_of_eq rightparameters_ 
             termty isSetType term selections selections
;;

let isSetType paramty = ((Pervasives.compare 
  (get_sort_type paramty)
  (Cic.Sort Cic.Prop)) != 0) 

exception EqualityNotDefinedYet
let private_inversion_tac ~term selections =
 let module T = CicTypeChecker in
 let module R = CicReduction in
 let module C = Cic in
 let module P = PrimitiveTactics in
 let module PET = ProofEngineTypes in
 let private_inversion_tac ~term (proof, goal) =
 
 (*DEBUG*) debug_print (lazy  ("private inversion begins"));
 let _,metasenv,_subst,_,_, _ = proof in
 let uri_of_eq =
  match LibraryObjects.eq_URI () with
     None -> raise EqualityNotDefinedYet
  | Some uri -> uri
 in
 let (_,context,goalty) = CicUtil.lookup_meta goal metasenv in
 let termty,_ = T.type_of_aux' metasenv context term CicUniv.oblivion_ugraph in
 let uri = baseuri_of_term termty in  
 let o,_ = CicEnvironment.get_obj CicUniv.oblivion_ugraph uri in
 let (_,_,typeno,_) =
  match termty with
   C.MutInd (uri,typeno,exp_named_subst) -> (uri,exp_named_subst,typeno,[])
   | C.Appl ((C.MutInd (uri,typeno,exp_named_subst))::args) ->
    (uri,exp_named_subst,typeno,args)
   | _ -> raise NotAnInductiveTypeToEliminate
 in
 let buri = UriManager.buri_of_uri uri in
 let name,nleft,paramty,cons_list =
  match o with
   C.InductiveDefinition (tys,_,nleft,_) ->
    let (name,_,paramty,cons_list) = List.nth tys typeno in
    (name,nleft,paramty,cons_list)
   |_ -> assert false
 in
 let eliminator_uri = 
  UriManager.uri_of_string (buri ^ "/" ^ name ^ "_ind" ^ ".con") 
 in
 let parameters = (List.tl (term_to_list termty)) in
 let parameters_tys =  
  (List.map 
   (fun t -> (
    match (T.type_of_aux' metasenv context t CicUniv.oblivion_ugraph) with
     (term,graph) -> term))
   parameters) 
 in
 let consno = List.length cons_list in
 let nright= ((List.length parameters)- nleft) in 
 let isSetType = isSetType paramty in
 let cut_term = foo_cut nleft parameters 
  parameters_tys goalty uri_of_eq selections in
 (*DEBUG*)  debug_print (lazy ("cut term " ^ CicPp.ppterm cut_term));
  debug_print (lazy ("CONTEXT before apply HCUT: " ^ 
   (CicMetaSubst.ppcontext ~metasenv [] context )));
  debug_print (lazy ("termty " ^ CicPp.ppterm termty));
 (* cut DXn=DXn \to GOAL *)
 let proof1,gl1 = PET.apply_tactic (P.cut_tac cut_term) (proof,goal) in
 (* apply Hcut ; reflexivity  *)
 let proof2, gl2 = PET.apply_tactic
  (Tacticals.then_
   ~start: (P.apply_tac (C.Rel 1)) (* apply Hcut *)
   ~continuation: (EqualityTactics.reflexivity_tac)
  ) (proof1, (List.hd gl1))
 in      
 (*DEBUG*) debug_print (lazy  ("after apply HCUT;reflexivity 
  in private inversion"));
 (* apply (ledx_ind( lambda x. lambda y, ...)) *)
 let t1,metasenv,_subst,t3,t4, attrs = proof2 in
 let goal2 = List.hd (List.tl gl1) in
 let (_,context,g2ty) = CicUtil.lookup_meta goal2 metasenv in
 (* rightparameters type list *)
 let rightparam_ty_l = (cut_first nleft parameters_tys) in
 (* rightparameters list *)
 let rightparameters= cut_first nleft parameters in
 debug_print 
  (lazy ("Right param: " ^ (CicPp.ppterm (Cic.Appl rightparameters))));
 let lambda_t = foo_lambda nright rightparam_ty_l nright rightparam_ty_l 
 rightparameters [] nright goalty uri_of_eq rightparameters termty isSetType
 term selections in 
 let t = foo_appl nleft (nright+consno) lambda_t eliminator_uri in
 debug_print (lazy ("Lambda_t: " ^ (CicPp.ppterm t)));
 debug_print (lazy ("Term: " ^ (CicPp.ppterm termty)));
 debug_print (lazy ("Body: " ^ (CicPp.ppterm goalty)));
 debug_print 
  (lazy ("Right param: " ^ (CicPp.ppterm (Cic.Appl rightparameters))));
 debug_print (lazy ("CONTEXT before refinement: " ^ 
  (CicMetaSubst.ppcontext ~metasenv [] context )));
  (*DEBUG*) debug_print (lazy  ("private inversion: term before refinement: " ^ 
   CicPp.ppterm t));
 let (ref_t,_,metasenv'',_) = CicRefine.type_of_aux' metasenv context t 
  CicUniv.oblivion_ugraph 
 in
 (*DEBUG*) debug_print (lazy  ("private inversion: termine after refinement: "
  ^ CicPp.ppterm ref_t));
 let proof2 = (t1,metasenv'',_subst,t3,t4, attrs) in
 let my_apply_tac =
  let my_apply_tac status =
   let proof,goals = 
    ProofEngineTypes.apply_tactic (P.apply_tac ref_t) status in
   let patched_new_goals =
    let (_,metasenv''',_subst,_,_, _) = proof in
    let new_goals = ProofEngineHelpers.compare_metasenvs
     ~oldmetasenv:metasenv ~newmetasenv:metasenv''
    in
    List.filter (function i -> List.exists (function (j,_,_) -> j=i) 
     metasenv''') new_goals @ goals
   in
   proof,patched_new_goals
  in
 ProofEngineTypes.mk_tactic my_apply_tac
 in
 let proof3,gl3 = 
 PET.apply_tactic
  (Tacticals.then_
   ~start:my_apply_tac   
   ~continuation: 
    (ReductionTactics.simpl_tac (ProofEngineTypes.conclusion_pattern(None)))) 
    (proof2,goal2) 
 in

 (proof3, gl3)
in	
ProofEngineTypes.mk_tactic (private_inversion_tac ~term)
;;


let inversion_tac ~term =
 let module T = CicTypeChecker in
 let module R = CicReduction in
 let module C = Cic in
 let module P = PrimitiveTactics in
 let module PET = ProofEngineTypes in
 let inversion_tac ~term (proof, goal) =
 (*DEBUG*) debug_print (lazy ("inversion begins"));
  let _,metasenv,_subst,_,_, _ = proof in
  let (_,context,goalty) = CicUtil.lookup_meta goal metasenv in
  let termty,_ = T.type_of_aux' metasenv context term CicUniv.oblivion_ugraph in
  let uri, typeno = 
    match termty with
      | Cic.MutInd (uri,typeno,_) 
      | Cic.Appl(Cic.MutInd (uri,typeno,_)::_) -> uri,typeno
      | _ -> assert false
  in
  (* let uri = baseuri_of_term termty in *)
  let obj,_ = CicEnvironment.get_obj CicUniv.oblivion_ugraph uri in
  let name,nleft,arity,cons_list =
   match obj with
    Cic.InductiveDefinition (tys,_,nleft,_) ->
     let (name,_,arity,cons_list) = List.nth tys typeno in 
        (name,nleft,arity,cons_list)
   |_ -> assert false
  in
  let buri = UriManager.buri_of_uri uri in
  let inversor_uri = 
   UriManager.uri_of_string (buri ^ "/" ^ name ^ "_inv" ^ ".con") in
  (* arity length = number  of parameters plus 1 *)
  let arity_length = (List.length (term_to_list termty)) in
  (* Check the existence of any right parameter. *)
  assert (arity_length > (nleft + 1));
  let appl_term arity_consno uri =
   let l = [] in
   let a = ref l in
   for n = 1 to arity_consno do
    a := (Cic.Implicit None)::(!a)
   done;
   (* apply    i_inv             ? ...?      H).     *)
   Cic.Appl ([Cic.Const(uri,[])] @ !a @ [term])
  in
  let t = appl_term (arity_length + (List.length cons_list)) inversor_uri in
  let (t1,metasenv,_subst,t3,t4, attrs) = proof in
  let (ref_t,_,metasenv'',_) = CicRefine.type_of_aux' metasenv context t
  CicUniv.oblivion_ugraph 
  in
  let proof = (t1,metasenv'',_subst,t3,t4, attrs) in
  let proof3,gl3 = 
     ProofEngineTypes.apply_tactic (P.apply_tac ref_t) (proof,goal) in
  let patched_new_goals =
     let (_,metasenv''',_subst,_,_, _) = proof3 in
     let new_goals = ProofEngineHelpers.compare_metasenvs
      ~oldmetasenv:metasenv ~newmetasenv:metasenv''
     in
     List.filter (function i -> List.exists (function (j,_,_) -> j=i) 
      metasenv''') new_goals @ gl3
    in
  (proof3, patched_new_goals)
 in	
ProofEngineTypes.mk_tactic (inversion_tac ~term)
;;
