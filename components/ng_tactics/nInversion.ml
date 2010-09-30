(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department, University of Bologna, Italy.                     
    ||I||                                                                
    ||T||  HELM is free software; you can redistribute it and/or         
    ||A||  modify it under the terms of the GNU General Public License   
    \   /  version 2 or (at your option) any later version.      
     \ /   This software is distributed as is, NO WARRANTY.     
      V_______________________________________________________________ *)

(* $Id: nCic.ml 9058 2008-10-13 17:42:30Z tassi $ *)

(*let pp m = prerr_endline (Lazy.force m);;*)
let pp _ = ();;

let fresh_name =
 let i = ref 0 in
 function () ->
  incr i;
  "z" ^ string_of_int !i
;;

let mk_id id =
 let id = if id = "_" then fresh_name () else id in
  CicNotationPt.Ident (id,None)
;;

let rec split_arity ~subst context te =
  match NCicReduction.whd ~subst context te with
   | NCic.Prod (name,so,ta) -> 
       split_arity ~subst ((name, (NCic.Decl so))::context) ta
   | t -> context, t
;;

let mk_appl =
 function
    [] -> assert false
  | [x] -> x
  | l -> CicNotationPt.Appl l
;;

let rec mk_prods l t =
  match l with
    [] -> t
  | hd::tl -> CicNotationPt.Binder (`Forall, (mk_id hd, None), mk_prods tl t)
;;

let rec mk_arrows ?(pattern=false) xs ys selection target = 
  match selection,xs,ys with
    [],[],[] -> target
  | false :: l,x::xs,y::ys -> mk_arrows ~pattern xs ys l target
  | true :: l,x::xs,y::ys  -> 
     CicNotationPt.Binder (`Forall, (mk_id "_", Some (mk_appl [if pattern then CicNotationPt.Implicit `JustOne else mk_id "eq" ; CicNotationPt.Implicit `JustOne;x;y])),
                           mk_arrows ~pattern xs ys l target)
  | _ -> raise (Invalid_argument "ninverter: the selection doesn't match the arity of the specified inductive type")
;;

let subst_metasenv_and_fix_names status =
  let u,h,metasenv, subst,o = status#obj in
  let o = 
    NCicUntrusted.map_obj_kind ~skip_body:true 
     (NCicUntrusted.apply_subst subst []) o
  in
   status#set_obj(u,h,NCicUntrusted.apply_subst_metasenv subst metasenv,subst,o)
;;

let mk_inverter name is_ind it leftno ?selection outsort status baseuri =
 pp (lazy ("leftno = " ^ string_of_int leftno));
 let _,ind_name,ty,cl = it in
 pp (lazy ("arity: " ^ NCicPp.ppterm ~metasenv:[] ~subst:[] ~context:[] ty));
 let ncons = List.length cl in
 (**)let params,ty = NCicReduction.split_prods ~subst:[] [] leftno ty in
 let params = List.rev_map (function name,_ -> mk_id name) params in
 pp (lazy ("lunghezza params = " ^ string_of_int (List.length params)));(**)
 let args,sort= split_arity ~subst:[] [] ty in
 pp (lazy ("arity sort: " ^ NCicPp.ppterm ~metasenv:[] ~subst:[] ~context:args sort));
 (**)let args = List.rev_map (function name,_ -> mk_id name) args in
 pp (lazy ("lunghezza args = " ^ string_of_int (List.length args)));(**)
 let nparams = List.length args in

 pp (lazy ("nparams = " ^ string_of_int nparams));
 if nparams = 0 
   then raise (Failure "inverter: the type must have at least one right parameter") 
   else 
     let xs = List.map (fun n -> "x" ^ (string_of_int n)) (HExtlib.list_seq 1 (leftno+nparams+1)) in
     pp (lazy ("lunghezza xs = " ^ string_of_int (List.length xs)));
     let ls, rs = HExtlib.split_nth leftno xs in
     pp (lazy ("lunghezza ls = " ^ string_of_int (List.length ls)));
     pp (lazy ("lunghezza rs = " ^ string_of_int (List.length rs)));
     let ys = List.map (fun n -> "y" ^ (string_of_int n)) (HExtlib.list_seq (leftno+1) (leftno+nparams+1)) in
    
     let _id_xs = List.map mk_id xs in
     let id_ls = List.map mk_id ls in
     let id_rs = List.map mk_id rs in
     let id_ys = List.map mk_id ys in
    
     (* pseudocode  let t = Lambda y1 ... yr. xs_ = ys_ -> pred *)
    
     (* check: assuming we have more than one right parameter *) 
     (* pred := P yr- *)
     let pred = mk_appl ((mk_id "P")::id_ys) in
     
     let selection = match selection with 
         None -> HExtlib.mk_list true (List.length ys) 
       | Some s -> s
     in
     let prods = mk_arrows id_rs id_ys selection pred in
    
     let hyplist = 
       let rec hypaux k = function
           0 -> []
         | n -> ("H" ^ string_of_int k) :: hypaux (k+1) (n-1)
       in (hypaux 1 ncons)
     in
     pp (lazy ("lunghezza ys = " ^ string_of_int (List.length ys)));
    
     let outsort, suffix = NCicElim.ast_of_sort outsort in
     let theorem =
      mk_prods xs
       (CicNotationPt.Binder (`Forall, (mk_id "P", Some (mk_prods (HExtlib.mk_list "_" (List.length ys)) (CicNotationPt.Sort outsort))),
       mk_prods hyplist (CicNotationPt.Binder (`Forall, (mk_id "Hterm", Some (mk_appl (List.map mk_id (ind_name::xs)))), mk_appl (mk_id "P"::id_rs)))))
     in
     let status, theorem =
      GrafiteDisambiguate.disambiguate_nobj status ~baseuri 
       (baseuri ^ name ^ ".def",0,
         CicNotationPt.Theorem
          (`Theorem,name,theorem,
            Some (CicNotationPt.Implicit (`Tagged "inv")),`InversionPrinciple))
     in 
     let uri,height,nmenv,nsubst,nobj = theorem in
     let ninitial_stack = Continuationals.Stack.of_nmetasenv nmenv in
     let status = status#set_obj theorem in
     let status = status#set_stack ninitial_stack in
     let status = subst_metasenv_and_fix_names status in
    
     let cut_theorem = 
       let rs = List.map (fun x -> mk_id x) rs in
         mk_arrows rs rs selection (mk_appl (mk_id "P"::rs)) in
    
     let cut = mk_appl [CicNotationPt.Binder (`Lambda, (mk_id "Hcut", Some cut_theorem),
                        
CicNotationPt.Implicit (`Tagged "end"));
                        CicNotationPt.Implicit (`Tagged "cut")] in
     let intros = List.map (fun x -> pp (lazy x); NTactics.intro_tac x) (xs@["P"]@hyplist@["Hterm"]) in
     let where =
      "",0,(None,[],
       Some (
        mk_arrows ~pattern:true
         (HExtlib.mk_list (CicNotationPt.Implicit `JustOne) (List.length ys))
         (HExtlib.mk_list CicNotationPt.UserInput (List.length ys))
         selection CicNotationPt.UserInput)) in
     let elim_tac = if is_ind then NTactics.elim_tac else NTactics.cases_tac in
     let status =
      NTactics.block_tac 
       (NTactics.branch_tac ::
        NTactics.case_tac "inv" :: 
        (intros @
         [NTactics.apply_tac ("",0,cut);
          NTactics.branch_tac;
          NTactics.case_tac "end";
          NTactics.apply_tac ("",0,mk_id "Hcut");
          NTactics.apply_tac ("",0,mk_id "refl"); 
          NTactics.shift_tac;
          elim_tac ~what:("",0,mk_id "Hterm") ~where;
          NTactics.branch_tac ~force:true] @ 
           HExtlib.list_concat ~sep:[NTactics.shift_tac]
            (List.map (fun id-> [NTactics.apply_tac ("",0,mk_id id)]) hyplist) @
         [NTactics.merge_tac;
          NTactics.merge_tac;
          NTactics.merge_tac;
          NTactics.skip_tac])) status in
     pp (lazy "inv 3");
     status,status#obj
;;

