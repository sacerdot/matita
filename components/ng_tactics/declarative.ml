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
  | (g1, _, k, tag1) :: tl ->
    let goals = filter_open g1 in
    let (loc::tl) = goals in 
    let goal = goal_of_loc (loc) in
    goal ;;
  (*
  let (_,_,metasenv,_,_) = status#obj in
  match metasenv with
  | [] -> fail (lazy "There's nothing to prove")
  | (hd,_) :: tl -> hd
  *)

let extract_conclusion_type status goal =
  let gty = get_goalty status goal in
  let ctx = ctx_of gty in
  let status,gty = term_of_cic_term status gty ctx in
  gty
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
  let status,cicterm1 = disambiguate status ctx ty1 `XTNone (*(`XTSome (mk_cic_term ctx t))*) in
  let status,cicterm2 = disambiguate status ctx ty2 `XTNone (*(`XTSome (mk_cic_term ctx t))*) in
  NTacStatus.are_convertible status ctx cicterm1 cicterm2

(* LCF-like tactic that checks whether the conclusion of the sequent of the given goal is a product, checks that
   the type of the conclusion's bound variable is the same as t1 and then uses an exact_tac with
   \lambda id: t1. ?. If a t2 is given it checks that t1 ~_{\beta} t2 and uses and exact_tac with \lambda id: t2. ?
*)
let lambda_abstract_tac id t1 t2 status goal =
  match extract_conclusion_type status goal with
  | NCic.Prod (_,t,_) ->
    if alpha_eq_tacterm_kerterm t1 t status goal then
      match t2 with
      | None ->
        let (_,_,t1) = t1 in
        exact_tac ("",0,(Ast.Binder (`Lambda,(Ast.Ident (id,None),Some t1),Ast.Implicit
                                       `JustOne))) (*status*)
      | Some t2 ->
        let status,res = are_convertible t1 t2 status goal in
        if res then
          let (_,_,t2) = t2 in
          exact_tac ("",0,(Ast.Binder (`Lambda,(Ast.Ident (id,None),Some t2),Ast.Implicit
                                         `JustOne))) (*status*)
        else
          raise NotEquivalentTypes
    else
      raise FirstTypeWrong
  | _ -> raise NotAProduct

let assume name ty eqty (*status*) =
(*   let goal = extract_first_goal_from_status status in *)
  distribute_tac (fun status goal -> 
    try exec (lambda_abstract_tac name ty eqty status goal) status goal
    with
    | NotAProduct -> fail (lazy "You can't assume without an universal quantification")
    | FirstTypeWrong ->  fail (lazy "The assumed type is wrong")
    | NotEquivalentTypes -> fail (lazy "The two given types are not equivalent")
  )
;;

let suppose t1 id t2 (*status*) =
(*   let goal = extract_first_goal_from_status status in *)
  distribute_tac (fun status goal ->
    try exec (lambda_abstract_tac id t1 t2 status goal) status goal
    with
    | NotAProduct -> fail (lazy "You can't suppose without a logical implication")
    | FirstTypeWrong ->  fail (lazy "The supposed proposition is different from the premise")
    | NotEquivalentTypes -> fail (lazy "The two given propositions are not equivalent")
  )
;;

let assert_tac t1 t2 status goal continuation =
  let t = extract_conclusion_type status goal in
  if alpha_eq_tacterm_kerterm t1 t status goal then
    match t2 with
    | None -> continuation
    | Some t2 ->
      let status,res = are_convertible t1 t2 status goal in
      if res then continuation
      else
        raise NotEquivalentTypes
  else
    raise FirstTypeWrong

let mustdot status =
  let s = status#stack in
  match s with
  | [] -> fail (lazy "No goals to dot")
  | (_, _, k, _) :: tl ->
    if List.length k > 0 then
      true
    else
      false

let bydone just status =
  let goal = extract_first_goal_from_status status in
  let mustdot = mustdot status in
(*
  let goal,mustdot =
    let s = status#stack in
    match s with
    | [] -> fail (lazy "Invalid use of done")
    | (g1, _, k, tag1) :: tl ->
      let goals = filter_open g1 in
      let (loc::tl) = goals in 
      let goal = goal_of_loc (loc) in
      if List.length k > 0 then
        goal,true
      else
        goal,false
  in

   *)
(*
      let goals = filter_open g1 in
      let (loc::tl) = goals in 
      let goal = goal_of_loc (loc) in
      if tag1 == `BranchTag then
        if List.length (shift_goals s) > 0 then (* must simply shift *)
          (
            prerr_endline (pp status#stack); 
            prerr_endline "Head goals:";
            List.map (fun goal -> prerr_endline (string_of_int goal)) (head_goals status#stack);
            prerr_endline "Shift goals:";
            List.map (fun goal -> prerr_endline (string_of_int goal)) (shift_goals status#stack);
            prerr_endline "Open goals:";
            List.map (fun goal -> prerr_endline (string_of_int goal)) (open_goals status#stack);
            if tag2 == `BranchTag && g2 <> [] then 
              goal,true,false,false
            else if tag2 == `BranchTag then
              goal,false,true,true
            else
              goal,false,true,false
          )
        else
          (
           if tag2 == `BranchTag then
              goal,false,true,true
            else
              goal,false,true,false
          )
      else
        goal,false,false,false (* It's a strange situation, there's is an underlying level on the
                                  stack but the current one was not created by a branch? Should be
                                  an error *)
    | (g, _, _, tag) :: [] ->
      let (loc::tl) = filter_open g in 
      let goal = goal_of_loc (loc) in
      if tag == `BranchTag then
(*         let goals = filter_open g in *)
          goal,false,true,false
      else
        goal,false,false,false 
  in
   *)
  let l = [mk_just status goal just] in
  let l =
    if mustdot then List.append l [dot_tac] else l
  in
  (*
  let l =
    if mustmerge then List.append l [merge_tac] else l
  in
  let l =
    if mustmergetwice then List.append l [merge_tac]  else l
  in 
     *)
    block_tac l status
(*
  let (_,_,metasenv,subst,_) = status#obj in
  let goal,last =
    match metasenv with
    | [] -> fail (lazy "There's nothing to prove")
    | (_,_) :: (hd,_) :: tl -> hd,false
    | (hd,_) :: tl -> hd,true
  in
  if last then
    mk_just status goal just status
  else
    block_tac [ mk_just status goal just; shift_tac ] status
*)
;;

let we_need_to_prove t id t1 status =
  let goal = extract_first_goal_from_status status in
  match id with
  | None ->
    (
      match t1 with
      | None ->  (* We need to prove t *)
        (
          try assert_tac t None status goal (id_tac status)
          with
          | FirstTypeWrong -> fail (lazy "The given proposition is not the same as the conclusion")
        )
      | Some t1 -> (* We need to prove t or equivalently t1 *)
        (
          try assert_tac t (Some t1) status goal (change_tac ~where:("",0,(None,[],Some
                                                                             Ast.UserInput)) ~with_what:t1 status)
          with
          | FirstTypeWrong -> fail (lazy "The given proposition is not the same as the conclusion")
          | NotEquivalentTypes -> fail (lazy "The given propositions are not equivalent")
        )
    )
  | Some id ->
    (
      match t1 with
      (* We need to prove t (id) *)
      | None -> block_tac [cut_tac t; branch_tac; shift_tac; intro_tac id; merge_tac;
                           dot_tac
                          ] status
      (* We need to prove t (id) or equivalently t1 *)
      | Some t1 ->  block_tac [cut_tac t; branch_tac ; change_tac ~where:("",0,(None,[],Some
                                                                                  Ast.UserInput))
                                 ~with_what:t1; shift_tac; intro_tac id; merge_tac;
                               dot_tac
                              ]
                      status
    )
;;

let by_just_we_proved just ty id ty' status =
  let goal = extract_first_goal_from_status status in
  let wrappedjust = just in
  let just = mk_just status goal just in
  match id with
  | None ->
    (match ty' with
     | None -> (* just we proved P done *)
       (
         try
           assert_tac ty None status goal (bydone wrappedjust status)
         with
         | FirstTypeWrong -> fail (lazy "The given proposition is not the same as the conclusion")
         | NotEquivalentTypes -> fail (lazy "The given propositions are not equivalent")
       )
     | Some ty' -> (* just we proved P that is equivalent to P' done *)
       (
         try
           assert_tac ty' None status goal (block_tac [change_tac ~where:("",0,(None,[],Some
                                                                                       Ast.UserInput))
                                                              ~with_what:ty; bydone wrappedjust]
                                                   status )
         with
         | FirstTypeWrong -> fail (lazy "The second proposition is not the same as the conclusion")
         | NotEquivalentTypes -> fail (lazy "The given propositions are not equivalent")
       )
    )
  | Some id ->
    (
      match ty' with
      | None -> block_tac [cut_tac ty; branch_tac; just; shift_tac; intro_tac id; merge_tac ] status
      | Some ty' -> block_tac [cut_tac ty; branch_tac; just; shift_tac; intro_tac id; change_tac
                                 ~where:("",0,(None,[id,Ast.UserInput],None)) ~with_what:ty';
                               merge_tac] status
    )
;;

let existselim just id1 t1 t2 id2 (*status*) =
  distribute_tac (fun status goal ->
    let (_,_,t1) = t1 in
    let (_,_,t2) = t2 in
    let just = mk_just status goal just in
    exec (block_tac [
      cut_tac ("",0,(Ast.Appl [Ast.Ident ("ex",None); t1; Ast.Binder (`Lambda,(Ast.Ident
                                                                                 (id1,None), Some t1),t2)]));
      branch_tac ~force:false;
      just;
      shift_tac;
      case1_tac "_";
      intros_tac ~names_ref:(ref []) [id1;id2];
      merge_tac
    ]) status goal
  )
;;

let andelim just t1 id1 t2 id2 (*status*) =
(*   let goal = extract_first_goal_from_status status in *)
  distribute_tac (fun status goal ->
    let (_,_,t1) = t1 in
    let (_,_,t2) = t2 in
    let just = mk_just status goal just in
    exec (block_tac [
      cut_tac ("",0,(Ast.Appl [Ast.Ident ("And",None); t1 ; t2]));
      branch_tac ~force:false;
      just;
      shift_tac;
      case1_tac "_";
      intros_tac ~names_ref:(ref []) [id1;id2];
      merge_tac
    ]) status goal
  )
;;

let type_of_tactic_term status ctx t =
  let status,cicterm = disambiguate status ctx t `XTNone in
  let (_,cicty) = typeof status ctx cicterm in
  cicty

let swap_first_two_goals_tac status =
  let gstatus =
    match status#stack with
    | [] -> assert false
    | (g,t,k,tag) :: s ->
      match g with
      | (loc1) :: (loc2) :: tl ->
        ([loc2;loc1] @+ tl,t,k,tag) :: s
      | _ -> assert false
  in
  status#set_stack gstatus

let thesisbecomes t1 t2 = we_need_to_prove t1 None t2
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
                branch_tac; shift_tac; shift_tac; intro_tac id; merge_tac; dot_tac;
              ]
          status
;;

let conclude t1 =
  distribute_tac (fun status goal ->
    let cicgty = get_goalty status goal in
    let ctx = ctx_of cicgty in
    let _,gty = term_of_cic_term status cicgty ctx in
    match gty with
      NCic.Appl [_;_;plhs;_] ->
      if alpha_eq_tacterm_kerterm t1 plhs status goal then
        exec id_tac status goal
      else
        fail (lazy "The given conclusion is different from the left-hand side of the current conclusion")
    | _ -> fail (lazy "Your conclusion needs to be an equality")
    )
;;

let rewritingstep rhs just last_step status =
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
      (*CSC:manca controllo sul fatto che rhs sia convertibile con prhs*)
      let todo = [just'] in
      let todo = if mustdot status then List.append todo [dot_tac] else todo
      in
      block_tac todo
    else
      let (_,_,rhs) = rhs in
      block_tac [apply_tac ("",0,Ast.Appl [Ast.Ident ("trans_eq",None); Ast.NCic ty; Ast.NCic plhs;
                                           rhs; Ast.NCic prhs]); branch_tac; just'; merge_tac]
  in
  prepare continuation
;;

(*
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
    match lhs with
      None -> (* = E2 *)
      let plhs,prhs =
        match gty with (* Extracting the lhs and rhs of the previous equality *)
          NCic.Appl [_;_;plhs;prhs] -> plhs,prhs
        | _ -> fail (lazy "You are not building an equaility chain")
      in
      plhs,prhs,
      (fun continuation -> continuation status)
    | Some (None,lhs) -> (* conclude *) 
      let plhs,prhs =
        match gty with
          NCic.Appl [_;_;plhs;prhs] -> plhs,prhs
        | _ -> fail (lazy "You are not building an equaility chain")
      in
      (*TODO*)
      (*CSC: manca check plhs convertibile con lhs *)
      plhs,prhs,
      (fun continuation -> continuation status)
    | Some (Some name,lhs) -> (* obtain *)
      NCic.Rel 1, NCic.Rel 1, (* continuation for this case is gonna be ignored, so it doesn't
                                 matter what the values of these two are *)
      (fun continuation ->
         let (_,_,lhs) = lhs in
        block_tac [ cut_tac ("",0,(Ast.Appl [Ast.Ident ("eq",None); Ast.NCic ty; lhs; Ast.Implicit
                                              `JustOne])); 
                   swap_first_two_goals_tac;
                   branch_tac; shift_tac; shift_tac; intro_tac name; merge_tac; dot_tac;
(*
                   change_tac ~where:("",0,(None,[],Some Ast.Appl[Ast.Implicit `JustOne;Ast.Implicit
                                                                 `JustOne; Ast.UserInput; Ast.Implicit `JustOne]))
                                         ~with_what:rhs
*)
                 ]
          status
      )
  in
  let continuation =
    if last_step then
      (*CSC:manca controllo sul fatto che rhs sia convertibile con prhs*)
      let todo = [just'] in
      let todo = if mustdot status then List.append todo [dot_tac] else todo
      in
        block_tac todo
    else
      let (_,_,rhs) = rhs in
      block_tac [apply_tac ("",0,Ast.Appl [Ast.Ident ("trans_eq",None); Ast.NCic ty; Ast.NCic plhs;
                                           rhs; Ast.NCic prhs]); branch_tac; just'; merge_tac]
  in
    prepare continuation
;;
   *)

let we_proceed_by_cases_on t1 t2 status = 
  let goal = extract_first_goal_from_status status in
  try
    assert_tac t2 None status goal (block_tac [cases_tac ~what:t1 ~where:("",0,(None,[],Some
                                                                               Ast.UserInput));
                                             dot_tac] status)
  with
  | FirstTypeWrong -> fail (lazy "What you want to prove is different from the conclusion")

let we_proceed_by_induction_on t1 t2 status =
  let goal = extract_first_goal_from_status status in
  try
    assert_tac t2 None status goal (block_tac [elim_tac ~what:t1 ~where:("",0,(None,[],Some
                                                                               Ast.UserInput));
                                             dot_tac] status)
  with
  | FirstTypeWrong -> fail (lazy "What you want to prove is different from the conclusion")
;;

let byinduction t1 id = suppose t1 id None ;;

let case id l = 
  distribute_tac (fun status goal ->
    let rec aux l =
      match l with 
        [] -> [id_tac]
      | (id,ty)::tl ->
        (try_tac (assume id ("",0,ty) None)) :: (aux tl)
    in
(*     if l == [] then exec (try_tac (intro_tac "H")) status goal *)
(*         else  *)
    exec (block_tac (aux l)) status goal
    )
;;

let print_stack status = prerr_endline ("PRINT STACK: " ^ (pp status#stack)); id_tac status ;;

(* vim: ts=2: sw=0: et:
 * *)
