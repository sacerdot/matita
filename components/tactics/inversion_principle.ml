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

let debug = false;; 
let debug_print =
 fun msg -> if debug then prerr_endline (Lazy.force msg) else ()

(* cuts away the last element of a list 'l' *)
let rec cut_last l =
 match l with
 | hd::tl when tl != [] -> hd:: (cut_last tl)
 | _ -> []
;;

(* cuts away the first 'n' elements of a list 'l' *)
let rec cut_first n l =
 if n>0 then
  match l with
   | hd::tl -> cut_first (n-1) tl
   | [] -> []
 else l
;;

(* returns the first 'n' elements of a list 'l' *)
let rec takefirst n l =
 if n > 0 then
  match l with
   hd::tl when n > 0 -> hd:: takefirst (n-1) tl
  | _ -> assert false
 else []
;;

(* from a complex Cic.Prod term, returns the list of its components *)
let rec list_of_prod term =
 match term with
  | Cic.Prod (_,src,tgt) -> src::(list_of_prod tgt)
  | _ -> [term]
;;

let rec build_metas sort cons_list created_vars right_created_vars prop
 uri typeno =
 match cons_list with
  | hd::tl -> 
   Cic.Prod(
    Cic.Anonymous, 
    Cic.Implicit None, 
    build_metas sort tl
     (List.map (CicSubstitution.lift 1) created_vars) 
     (List.map (CicSubstitution.lift 1) right_created_vars) 
     (List.map (CicSubstitution.lift 1) prop) uri typeno)
  | [] ->  
   Cic.Prod(
    Cic.Name("H"), (*new name?*)
    Cic.Appl([Cic.MutInd(uri, typeno, [])] @ created_vars), 
    Cic.Appl (( (List.map (CicSubstitution.lift 1) prop)  @ 
     (List.map (CicSubstitution.lift 1 ) right_created_vars) @
      (if Inversion.isSetType sort then [Cic.Rel 1] else [])(*H*))
  )) 
;;

(* computes the type of the abstract P *)
let rec get_prop_arity sort rightparam_tys(*only to name m's*) created_vars_ty 
 local_rvars left_created_vars nleft uri typeno =
  match (created_vars_ty) with
  hd::tl when (nleft > 0) ->
   get_prop_arity sort rightparam_tys tl local_rvars left_created_vars 
    (nleft-1) uri typeno
  | hd::tl ->
   Cic.Prod(
    Cic.Name("m" ^  string_of_int(List.length rightparam_tys) ),
    hd,
    get_prop_arity sort (List.tl rightparam_tys) 
     (List.map (CicSubstitution.lift 1) tl)
     (List.map (CicSubstitution.lift 1) (local_rvars @ [Cic.Rel 1]))
     (List.map (CicSubstitution.lift 1) left_created_vars) nleft uri typeno
   )
  | [] -> 
   if Inversion.isSetType sort then
    Cic.Prod(Cic.Anonymous,
     Cic.Appl([Cic.MutInd(uri, typeno, [])] 
      @ (List.map (CicSubstitution.lift (-1)) left_created_vars)
      @ (List.map (CicSubstitution.lift(-1)) local_rvars)  ),
     Cic.Sort(Cic.Prop))
   else
    Cic.Sort Cic.Prop
;;

(* created vars is empty at the beginning *)
let rec build_theorem rightparam_tys arity_l (*arity_l only to name p's*)
 arity cons_list created_vars created_vars_ty nleft
 uri typeno = 
  match (arity) with
  Cic.Prod(_,src,tgt) -> 
   Cic.Prod(
    Cic.Name("p" ^  string_of_int(List.length arity_l)),
    src,
    build_theorem rightparam_tys 
    (List.tl arity_l) tgt cons_list 
    (List.map (CicSubstitution.lift 1) (created_vars @ [Cic.Rel 1])) 
    (List.map (CicSubstitution.lift 1) (created_vars_ty @ [src]))
     nleft uri typeno) 
  | sort ->  
   Cic.Prod(Cic.Name("P"), 
    get_prop_arity sort rightparam_tys created_vars_ty [](*local vars*) 
     (takefirst nleft created_vars) (*left_created_vars*) nleft uri typeno, 
    build_metas sort cons_list created_vars (cut_first nleft created_vars)
    [(Cic.Rel 1)] uri typeno ) 
;;

let build_one typeno inversor_uri indty_uri nleft arity cons_list selections =
 (*check if there are right parameters, else return void*)
 if List.length (list_of_prod arity) = (nleft + 1) then
  None
 else
  try
         let arity_l = cut_last (list_of_prod arity) in
         let rightparam_tys = cut_first nleft arity_l in
         let theorem = build_theorem rightparam_tys arity_l arity cons_list 
          [](*created_vars*) [](*created_vars_ty*) nleft indty_uri typeno in
         debug_print 
          (lazy ("theorem prima di refine: " ^ (CicPp.ppterm theorem)));
         let (ref_theorem,_,metasenv,_) =
    CicRefine.type_of_aux' [] [] theorem CicUniv.oblivion_ugraph in
         (*DEBUG*) debug_print 
           (lazy ("theorem dopo refine: " ^ (CicPp.ppterm ref_theorem)));
         let goal = CicMkImplicit.new_meta metasenv [] in
         let metasenv' = (goal,[],ref_theorem)::metasenv in
         let attrs = [`Class (`InversionPrinciple); `Generated] in
   let _subst = [] in
         let proof= 
          Some inversor_uri,metasenv',_subst,
     lazy (Cic.Meta(goal,[])),ref_theorem, attrs in 
         let _,applies =
          List.fold_right
  	       (fun _ (i,applies) ->
       i+1,PrimitiveTactics.apply_tac (Cic.Rel i)::applies
     ) cons_list (2,[]) in
         let proof1,gl1 = 
          ProofEngineTypes.apply_tactic
  	       (Tacticals.then_
  	         ~start:(PrimitiveTactics.intros_tac ())
  	         (*if the number of applies is 1, we cannot use 
  	           thens, but then_*)
  	         ~continuation:
  	           (match List.length applies with
  		            0 -> Inversion.private_inversion_tac (Cic.Rel 1) selections
  	            | 1 ->
            Tacticals.then_
  			           ~start:(Inversion.private_inversion_tac (Cic.Rel 1) selections)
  			       ~continuation:(PrimitiveTactics.apply_tac (Cic.Rel 2))
  	            | _ ->
            Tacticals.thens
			           ~start:(Inversion.private_inversion_tac (Cic.Rel 1) selections)
			           ~continuations:applies))
	       (proof,goal) in
   let _,metasenv,_subst,bo,ty, attrs = proof1 in
         assert (metasenv = []);
         Some
  	      (inversor_uri,
  	       Cic.Constant 
  	        (UriManager.name_of_uri inversor_uri,Some (Lazy.force bo),ty,[],[]))
  with
           Inversion.EqualityNotDefinedYet -> 
       HLog.warn "No default equality, no inversion principle";
       None
   | CicRefine.RefineFailure ls ->
     HLog.warn
      ("CicRefine.RefineFailure during generation of inversion principle: " ^
       Lazy.force ls) ;
     None
   | CicRefine.Uncertain ls ->
     HLog.warn
      ("CicRefine.Uncertain during generation of inversion principle: " ^
       Lazy.force ls) ;
     None
   | CicRefine.AssertFailure ls ->
     HLog.warn
      ("CicRefine.AssertFailure during generation of inversion principle: " ^
       Lazy.force ls) ;
     None
;;

let build_inverter ~add_obj status u indty_uri params =
  let indty_uri, indty_no, _ = UriManager.ind_uri_split indty_uri in
  let indty_no = match indty_no with None -> raise (Invalid_argument "not an inductive type")| Some n -> n in
  let indty, univ = CicEnvironment.get_cooked_obj CicUniv.empty_ugraph indty_uri
  in
  match indty with
  | Cic.InductiveDefinition (tys,_,nleft,attrs) ->
     let _,inductive,_,_ = List.hd tys in
     if not inductive then raise (Invalid_argument "not an inductive type")
     else
     let name,_,arity,cons_list = List.nth tys (indty_no-1) in 
      (match build_one (indty_no-1) u indty_uri nleft arity cons_list params with
       | None -> status,[]
       | Some (uri, obj) ->
           let status, added = add_obj uri obj status in
           status, uri::added)
  | _ -> assert false
;;

let build_inversion ~add_obj ~add_coercion uri obj =
 match obj with
  | Cic.InductiveDefinition (tys,_,nleft,attrs) ->
     let _,inductive,_,_ = List.hd tys in
     if not inductive then []
     else
       let counter = ref (List.length tys) in
       let all_inverters =
	      List.fold_right 
	       (fun (name,_,arity,cons_list) res ->
         let arity_l = cut_last (list_of_prod arity) in
         let rightparam_tys = cut_first nleft arity_l in
         let params = HExtlib.mk_list true (List.length rightparam_tys) in
         let buri = UriManager.buri_of_uri uri in
         let inversor_uri = 
           UriManager.uri_of_string (buri ^ "/" ^ name ^ "_inv" ^ ".con") in
           counter := !counter-1;
	         match build_one !counter inversor_uri uri nleft arity cons_list params with
		          None -> res 
		        | Some inv -> inv::res
         ) tys []
       in
       List.fold_left
        (fun lemmas (uri,obj) -> add_obj uri obj @ uri :: lemmas
        ) [] all_inverters
  | _ -> []
;;

let init () =
  LibrarySync.add_object_declaration_hook build_inversion;;
