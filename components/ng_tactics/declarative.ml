(* Copyright (C) 2019, HELM Team.
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

open Continuationals.Stack
module Ast = NotationPt
open NTactics
open NTacStatus

type just = [ `Term of NTacStatus.tactic_term | `Auto of NnAuto.auto_params ]

let mk_just status goal =
  function
    `Auto (l,params) -> NnAuto.auto_lowtac ~params:(l,params) status goal
  | `Term t -> apply_tac t

exception NotAProduct
exception FirstTypeWrong
exception NotEquivalentTypes

let extract_first_goal_from_status status =
  let s = status#stack in
  match s with
  | [] -> fail (lazy "There's nothing to prove")
  | (g1, _, _k, _tag1, _) :: _tl ->
    let goals = filter_open g1 in
    match goals with
      [] -> fail (lazy "No goals under focus")
    | loc::_tl -> 
      let goal = goal_of_loc (loc) in
      goal ;;

let extract_conclusion_type status goal =
  let gty = get_goalty status goal in
  let ctx = ctx_of gty in
  term_of_cic_term status gty ctx
;;

let alpha_eq_tacterm_kerterm ty t status goal =
  let gty = get_goalty status goal in
  let ctx = ctx_of gty in
  let status,cicterm = disambiguate status ctx ty `XTNone (*(`XTSome (mk_cic_term ctx t))*) in
  let (_,_,metasenv,subst,_) = status#obj in
  let status,ty = term_of_cic_term status cicterm ctx in
  if NCicReduction.alpha_eq status metasenv subst ctx t ty then
    true
  else
    false
;;

let are_convertible ty1 ty2 status goal =
  let gty = get_goalty status goal in
  let ctx = ctx_of gty in
  let status,cicterm1 = disambiguate status ctx ty1 `XTNone in
  let status,cicterm2 = disambiguate status ctx ty2 `XTNone in
  NTacStatus.are_convertible status ctx cicterm1 cicterm2

let clear_volatile_params_tac status =
  match status#stack with
    [] -> fail (lazy "Empty stack")
  | (g,t,k,tag,p)::tl -> 
    let rec remove_volatile = function
        [] -> []
      | (k,_v as hd')::tl' ->
        let re = Str.regexp "volatile_.*" in
        if Str.string_match re k 0 then
          remove_volatile tl'
        else
          hd'::(remove_volatile tl')
    in
    let newp = remove_volatile p in
    status#set_stack ((g,t,k,tag,newp)::tl)
;;

let add_parameter_tac key value status =
  match status#stack with
    [] -> status
  | (g,t,k,tag,p) :: tl -> status#set_stack ((g,t,k,tag,(key,value)::p)::tl)
;;


(* LCF-like tactic that checks whether the conclusion of the sequent of the given goal is a product, checks that
   the type of the conclusion's bound variable is the same as t1 and then uses an exact_tac with
   \lambda id: t1. ?. If a t2 is given it checks that t1 ~_{\beta} t2 and uses and exact_tac with \lambda id: t2. ?
*)
let lambda_abstract_tac id t1 status goal =
  match extract_conclusion_type status goal with
  | status,NCic.Prod (_,t,_) ->
    if alpha_eq_tacterm_kerterm t1 t status goal then
      let (_,_,t1) = t1 in
      block_tac [exact_tac ("",0,(Ast.Binder (`Lambda,(Ast.Ident (id,None),Some t1),Ast.Implicit
                                                `JustOne))); clear_volatile_params_tac;
                 add_parameter_tac "volatile_newhypo" id] status
    else
      raise FirstTypeWrong
  | _ -> raise NotAProduct

let assume name ty status =
  let goal = extract_first_goal_from_status status in
  try lambda_abstract_tac name ty status goal
  with
  | NotAProduct -> fail (lazy "You can't assume without an universal quantification")
  | FirstTypeWrong ->  fail (lazy "The assumed type is wrong")
  | NotEquivalentTypes -> fail (lazy "The two given types are not equivalent")
;;

let suppose t1 id status =
  let goal = extract_first_goal_from_status status in
  try lambda_abstract_tac id t1 status goal
  with
  | NotAProduct -> fail (lazy "You can't suppose without a logical implication")
  | FirstTypeWrong ->  fail (lazy "The supposed proposition is different from the premise")
  | NotEquivalentTypes -> fail (lazy "The two given propositions are not equivalent")
;;

let assert_tac t1 t2 status goal continuation =
  let status,t = extract_conclusion_type status goal in
  if alpha_eq_tacterm_kerterm t1 t status goal then
    match t2 with
    | None -> continuation
    | Some t2 ->
      let _status,res = are_convertible t1 t2 status goal in
      if res then continuation
      else
        raise NotEquivalentTypes
  else
    raise FirstTypeWrong

let branch_dot_tac status =
  match status#stack with 
    ([],t,k,tag,p) :: tl ->
    if List.length t > 0 then
      status#set_stack (([List.hd t],List.tl t,k,tag,p)::tl)
    else
      status
  | _ -> status
;;

let status_parameter key status =
  match status#stack with
    [] -> ""
  | (_g,_t,_k,_tag,p)::_ -> try List.assoc key p with _ -> ""
;;

let beta_rewriting_step t status =
  let ctx = status_parameter "volatile_context" status in
  if ctx <> "beta_rewrite" then 
    (
      let newhypo = status_parameter "volatile_newhypo" status in
      if newhypo = "" then
        fail (lazy "Invalid use of 'or equivalently'")
      else
        change_tac ~where:("",0,(None,[newhypo,Ast.UserInput],None)) ~with_what:t status
    )
  else
    change_tac ~where:("",0,(None,[],Some
                               Ast.UserInput)) ~with_what:t status
;;

let done_continuation status =
  let rec continuation l =
    match l with
      [] -> []
    | (_,t,_,tag,p)::tl ->
      if tag = `BranchTag then
        if List.length t > 0 then
          let continue =
            let ctx =
              try List.assoc "context" p
              with Not_found -> ""
            in
              ctx <> "induction" && ctx <> "cases"
          in
          if continue then [clear_volatile_params_tac;branch_dot_tac] else
            [clear_volatile_params_tac]
        else 
          [merge_tac] @ (continuation tl)
      else
        []
  in
    continuation status#stack
;;

let bydone just status =
  let goal = extract_first_goal_from_status status in
  let continuation = done_continuation status in
  let l = [mk_just status goal just] @ continuation in
  block_tac l status
;;

let push_goals_tac status = 
  match status#stack with
    [] -> fail (lazy "Error pushing goals")
  | (g1,t1,k1,tag1,p1) :: (g2,t2,k2,tag2,p2) :: tl ->
    if List.length g2 > 0 then
      status#set_stack ((g1,t1 @+ g2,k1,tag1,p1) :: ([],t2,k2,tag2,p2) :: tl)
    else status (* Nothing to push *)
  | _ -> status

let we_need_to_prove t id status =
  let goal = extract_first_goal_from_status status in
  match id with
  | None ->
    (
      try assert_tac t None status goal (add_parameter_tac "volatile_context" "beta_rewrite" status)
      with
      | FirstTypeWrong -> fail (lazy "The given proposition is not the same as the conclusion")
    )
  | Some id ->
    (
      block_tac [clear_volatile_params_tac; cut_tac t; branch_tac; shift_tac; intro_tac id; merge_tac; branch_tac;
                 push_goals_tac; add_parameter_tac "volatile_context" "beta_rewrite"
                          ] status
    )
;;

let by_just_we_proved just ty id status =
  let goal = extract_first_goal_from_status status in
  let just = mk_just status goal just in
  match id with
  | None ->
    assert_tac ty None status goal (block_tac [clear_volatile_params_tac; add_parameter_tac
                                                 "volatile_context" "beta_rewrite"] status)
  | Some id ->
    (
      block_tac [cut_tac ty; branch_tac; just; shift_tac; intro_tac id; merge_tac;
                 clear_volatile_params_tac; add_parameter_tac "volatile_newhypo" id] status
    )
;;

let existselim just id1 t1 t2 id2 status =
  let goal = extract_first_goal_from_status status in
  let (_,_,t1) = t1 in
  let (_,_,t2) = t2 in
  let just = mk_just status goal just in
  (block_tac [
      cut_tac ("",0,(Ast.Appl [Ast.Ident ("ex",None); t1; Ast.Binder (`Lambda,(Ast.Ident
                                                                                 (id1,None), Some t1),t2)]));
      branch_tac ~force:false;
      just;
      shift_tac;
      case1_tac "_";
      intros_tac ~names_ref:(ref []) [id1;id2];
      merge_tac;
      clear_volatile_params_tac
    ]) status
;;

let andelim just t1 id1 t2 id2 status =
  let goal = extract_first_goal_from_status status in
  let (_,_,t1) = t1 in
  let (_,_,t2) = t2 in
  let just = mk_just status goal just in
  (block_tac [
      cut_tac ("",0,(Ast.Appl [Ast.Ident ("And",None); t1 ; t2]));
      branch_tac ~force:false;
      just;
      shift_tac;
      case1_tac "_";
      intros_tac ~names_ref:(ref []) [id1;id2];
      merge_tac;
      clear_volatile_params_tac
    ]) status
;;

let type_of_tactic_term status ctx t =
  let status,cicterm = disambiguate status ctx t `XTNone in
  let (_,cicty) = typeof status ctx cicterm in
  cicty

let swap_first_two_goals_tac status =
  let gstatus =
    match status#stack with
    | [] -> assert false
    | (g,t,k,tag,p) :: s ->
      match g with
      | (loc1) :: (loc2) :: tl ->
        ([loc2;loc1] @+ tl,t,k,tag,p) :: s
      | _ -> assert false
  in
  status#set_stack gstatus

let thesisbecomes t1 = we_need_to_prove t1 None
;;

let obtain id t1 status =
  let goal = extract_first_goal_from_status status in
  let cicgty = get_goalty status goal in
  let ctx = ctx_of cicgty in
  let cicty = type_of_tactic_term status ctx t1 in
  let _,ty = term_of_cic_term status cicty ctx in
  let (_,_,t1) = t1 in
  block_tac [ cut_tac ("",0,(Ast.Appl [Ast.Ident ("eq",None); Ast.NCic ty; t1; Ast.Implicit
                                         `JustOne]));
              swap_first_two_goals_tac;
              branch_tac; shift_tac; shift_tac; intro_tac id; merge_tac; branch_tac; push_goals_tac;
              add_parameter_tac "volatile_context" "rewrite"
            ]
    status
;;

let conclude t1 status =
  let goal = extract_first_goal_from_status status in
  let cicgty = get_goalty status goal in
  let ctx = ctx_of cicgty in
  let _,gty = term_of_cic_term status cicgty ctx in
  match gty with
    (* The first term of this Appl should probably be "eq" *)
    NCic.Appl [_;_;plhs;_] ->
    if alpha_eq_tacterm_kerterm t1 plhs status goal then
      add_parameter_tac "volatile_context" "rewrite" status
    else
      fail (lazy "The given conclusion is different from the left-hand side of the current conclusion")
  | _ -> fail (lazy "Your conclusion needs to be an equality")
;;

let rewritingstep rhs just last_step status =
  let ctx = status_parameter "volatile_context" status in
  if ctx = "rewrite" then 
    (
      let goal = extract_first_goal_from_status status in
      let cicgty = get_goalty status goal in
      let ctx = ctx_of cicgty in
      let _,gty = term_of_cic_term status cicgty ctx in
      let cicty = type_of_tactic_term status ctx rhs in
      let _,ty = term_of_cic_term status cicty ctx in
      let just' = (* Extraction of the ""justification"" from the ad hoc justification *)
        match just with
          `Auto (univ, params) ->
          let params =
            if not (List.mem_assoc "timeout" params) then
              ("timeout","3")::params
            else params
          in
          let params' =
            if not (List.mem_assoc "paramodulation" params) then
              ("paramodulation","1")::params
            else params
          in
          if params = params' then NnAuto.auto_lowtac ~params:(univ, params) status goal
          else
            first_tac [NnAuto.auto_lowtac ~params:(univ, params) status goal; NnAuto.auto_lowtac
                         ~params:(univ, params') status goal]
        | `Term just -> apply_tac just
        | `SolveWith term -> NnAuto.demod_tac ~params:(Some [term], ["all","1";"steps","1"; "use_ctx","false"])
        | `Proof -> id_tac
      in
      let plhs,prhs,prepare =
        match gty with (* Extracting the lhs and rhs of the previous equality *)
          NCic.Appl [_;_;plhs;prhs] -> plhs,prhs,(fun continuation -> continuation status)
        | _ -> fail (lazy "You are not building an equaility chain")
      in
      let continuation =
        if last_step then
          let todo = [just'] @ (done_continuation status) in
          block_tac todo
        else
          let (_,_,rhs) = rhs in
          block_tac [apply_tac ("",0,Ast.Appl [Ast.Ident ("trans_eq",None); Ast.NCic ty; Ast.NCic plhs;
                                               rhs; Ast.NCic prhs]); branch_tac; just'; merge_tac]
      in
      prepare continuation
    )
  else
    fail (lazy "You are not building an equality chain")
;;

let rec pp_metasenv_names (metasenv:NCic.metasenv) =
  match metasenv with
    [] -> ""
  | hd :: tl ->
    let n,conj = hd in
    let meta_attrs,_,_ = conj in
    let rec find_name_aux meta_attrs = match meta_attrs with
        [] -> "Anonymous"
      | hd :: tl -> match hd with
          `Name n -> n
        | _ -> find_name_aux tl
    in
    let name = find_name_aux meta_attrs
    in
    "[Goal: " ^ (string_of_int n) ^ ", Name: " ^ name ^ "]; " ^ (pp_metasenv_names tl)
;;

let print_goals_names_tac s (status:#NTacStatus.tac_status) =
  let (_,_,metasenv,_,_) = status#obj in
  prerr_endline (s ^" -> Metasenv: " ^ (pp_metasenv_names metasenv)); status

(* Useful as it does not change the order in the list *)
let rec list_change_assoc k v = function
    [] -> []
  | (k',_v' as hd) :: tl -> if k' = k then (k',v) :: tl else hd :: (list_change_assoc k v tl)
;;

let add_names_to_goals_tac (cl:NCic.constructor list ref) (status:#NTacStatus.tac_status) =
  let add_name_to_goal name goal metasenv =
    let (mattrs,ctx,t) = try List.assoc goal metasenv with _ -> assert false in
    let mattrs = (`Name name) :: (List.filter (function `Name _ -> false | _ -> true) mattrs) in
    let newconj = (mattrs,ctx,t) in
    list_change_assoc goal newconj metasenv
  in
  let new_goals =
    (* It's important that this tactic is called before branching and right after the creation of
     * the new goals, when they are still under focus *)
    match status#stack with
      [] -> fail (lazy "Can not add names to an empty stack")
    | (g,_,_,_,_) :: _tl -> 
      let rec sublist n = function
          [] -> []
        | hd :: tl -> if n = 0 then [] else hd :: (sublist (n-1) tl)
      in
      List.map (fun _,sw -> goal_of_switch sw) (sublist (List.length !cl) g)
  in
  let rec add_names_to_goals g cl metasenv =
    match g,cl with
      [],[] -> metasenv
    | hd::tl, (_,consname,_)::tl' -> 
      add_names_to_goals tl tl' (add_name_to_goal consname hd metasenv)
    | _,_ -> fail (lazy "There are less goals than constructors")
  in
  let (olduri,oldint,metasenv,oldsubst,oldkind) = status#obj in
  let newmetasenv = add_names_to_goals new_goals !cl metasenv
  in status#set_obj(olduri,oldint,newmetasenv,oldsubst,oldkind)
;;
(*
  let (olduri,oldint,metasenv,oldsubst,oldkind) = status#obj in
  let remove_name_from_metaattrs =
   List.filter (function `Name _ -> false | _ -> true) in
  let rec add_names_to_metasenv cl metasenv =
    match cl,metasenv with
      [],_ -> metasenv
    | hd :: tl, mhd :: mtl ->
      let _,consname,_ = hd in
        let gnum,conj = mhd in
        let mattrs,ctx,t = conj in
        let mattrs = [`Name consname] @ (remove_name_from_metaattrs mattrs)
        in
        let newconj = mattrs,ctx,t in
        let newmeta = gnum,newconj in
        newmeta :: (add_names_to_metasenv tl mtl)
    | _,[] -> assert false
  in
  let newmetasenv = add_names_to_metasenv !cl metasenv in
  status#set_obj (olduri,oldint,newmetasenv,oldsubst,oldkind)
*)

let unfocus_branch_tac status =
  match status#stack with
    [] -> status
  | (g,t,k,tag,p) :: tl -> status#set_stack (([],g @+ t,k,tag,p)::tl)
;;

let we_proceed_by_induction_on t1 t2 status =
  let goal = extract_first_goal_from_status status in
  let txt,len,t1 = t1 in
  let t1 = txt, len, Ast.Appl [t1; Ast.Implicit `Vector] in
  let indtyinfo = ref None in
  let sort = ref (NCic.Rel 1) in
  let cl = ref [] in (* this is a ref on purpose, as the block of code after sort_of_goal_tac in
  block_tac acts as a block of asynchronous code, in which cl gets modified with the info retrieved
  with analize_indty_tac, and later used to label each new goal with a costructor name. Using a
  plain list this doesn't seem to work, as add_names_to_goals_tac would immediately act on an empty
  list, instead of acting on the list of constructors *)
  try
    assert_tac t2 None status goal (block_tac [
        analyze_indty_tac ~what:t1 indtyinfo;
        sort_of_goal_tac sort;
        (fun status ->
           let ity = HExtlib.unopt !indtyinfo in
           let NReference.Ref (uri, _) = ref_of_indtyinfo ity in
           let name =
             NUri.name_of_uri uri ^ "_" ^
             snd (NCicElim.ast_of_sort
                    (match !sort with NCic.Sort x -> x | _ -> assert false))
           in
           let eliminator =
             let l = [Ast.Ident (name,None)] in
             (* Generating an implicit for each argument of the inductive type, plus one the
              * predicate, plus an implicit for each constructor of the inductive type *)
             let l = l @ HExtlib.mk_list (Ast.Implicit `JustOne) (ity.leftno+1+ity.consno) in
             let _,_,t1 = t1 in
             let l = l @ [t1] in
             Ast.Appl l
           in
           cl := ity.cl;
           exact_tac ("",0,eliminator) status);
        add_names_to_goals_tac cl; 
        branch_tac; 
        push_goals_tac;
        unfocus_branch_tac;
        add_parameter_tac "context" "induction"
      ] status)
  with
  | FirstTypeWrong -> fail (lazy "What you want to prove is different from the conclusion")
;;

let we_proceed_by_cases_on ((txt,len,ast1) as t1)  t2 status =
  let goal = extract_first_goal_from_status status in
  let npt1 = txt, len, Ast.Appl [ast1; Ast.Implicit `Vector] in
  let indtyinfo = ref None in
  let cl = ref [] in
  try
    assert_tac t2 None status goal (block_tac [
        analyze_indty_tac ~what:npt1 indtyinfo;
        cases_tac ~what:t1 ~where:("",0,(None,[],Some
                                           Ast.UserInput));
        (
          fun status ->
            let ity = HExtlib.unopt !indtyinfo in
            cl := ity.cl; add_names_to_goals_tac cl status
        );
        branch_tac; push_goals_tac;
        unfocus_branch_tac;
        add_parameter_tac "context" "cases"
      ] status)
  with
  | FirstTypeWrong -> fail (lazy "What you want to prove is different from the conclusion")
;;

let byinduction t1 id = suppose t1 id ;;

let name_of_conj conj =
  let mattrs,_,_ = conj in
  let rec search_name mattrs =
    match mattrs with
      [] -> "Anonymous"
    | hd::tl ->
      match hd with
        `Name n -> n
      | _ -> search_name tl
  in
  search_name mattrs

let rec loc_of_goal goal l =
  match l with
    [] -> fail (lazy "Reached the end")
  | hd :: tl ->
    let _,sw = hd in
    let g = goal_of_switch sw in
    if g = goal then hd
    else loc_of_goal goal tl
;;

let has_focused_goal status =
  match status#stack with
    [] -> false
  | ([],_,_,_,_) :: _tl -> false
  | _ -> true
;;

let focus_on_case_tac case status =
  let (_,_,metasenv,_,_) = status#obj in
  let rec goal_of_case case metasenv =
    match metasenv with
      [] -> fail (lazy "The given case does not exist")
    | (goal,conj) :: tl ->
      if name_of_conj conj = case then goal
      else goal_of_case case tl
  in
  let goal_to_focus = goal_of_case case metasenv in
  let gstatus =
    match status#stack with
      [] -> fail (lazy "There is nothing to prove")
    | (g,t,k,tag,p) :: s ->
      let loc = 
        try 
          loc_of_goal goal_to_focus t 
        with _ -> fail (lazy "The given case is not part of the current induction/cases analysis
        context")
      in
      let curloc = if has_focused_goal status then 
          let goal = extract_first_goal_from_status status in
          [loc_of_goal goal g]
        else []
      in
      (((g @- curloc) @+ [loc]),(curloc @+ (t @- [loc])),k,tag,p) :: s
  in 
  status#set_stack gstatus
;;

let case id l status =
  let ctx = status_parameter "context" status in
  if ctx <> "induction" && ctx <> "cases" then fail (lazy "You can't use case outside of an
  induction/cases analysis context")
else
  (
    if has_focused_goal status then fail (lazy "Finish the current case before switching")
    else
      (
(*
        let goal = extract_first_goal_from_status status in
        let (_,_,metasenv,_,_) = status#obj in
        let conj = NCicUtils.lookup_meta goal metasenv in
        let name = name_of_conj conj in
*)
        let continuation =
          let rec aux l =
            match l with
              [] -> [id_tac]
            | (id,ty)::tl ->
              (try_tac (assume id ("",0,ty))) :: (aux tl)
          in
          aux l
        in
(*         if name = id then block_tac continuation status *)
(*         else  *)
          block_tac ([focus_on_case_tac id] @ continuation) status
      )
  )
;;

let print_stack status = prerr_endline ("PRINT STACK: " ^ (pp status#stack)); id_tac status ;;

(* vim: ts=2: sw=0: et:
 * *)
