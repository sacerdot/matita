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

module Ast = NotationPt
open NTactics
open NTacStatus

type just = [ `Term of NTacStatus.tactic_term | `Auto of NTacStatus.tactic_term GrafiteAst.aauto_params ]

let mk_just =
    function
          `Auto (l,params) -> NnAuto.auto_tac ~params:(l,params) ?trace_ref:None
        | `Term t -> apply_tac t

let extract_conclusion_type status goal =
    let gty = get_goalty status goal in
    let ctx = ctx_of gty in
    let status,gty = term_of_cic_term status gty ctx in
    gty
;;

let same_type_as_conclusion ty t status goal =
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

let same_type t1 t2 status goal = 
    let gty = get_goalty status goal in
    let ctx = ctx_of gty in
    let status1,cicterm1 = disambiguate status ctx t1 `XTNone in
    let status1,term1 = term_of_cic_term status cicterm1 (ctx_of cicterm1) in
    let status2,cicterm2 = disambiguate status ctx t2 `XTNone in
    let status2,term2 = term_of_cic_term status cicterm2 (ctx_of cicterm2) in
    let (_,_,metasenv,subst,_) = status#obj in
    if NCicReduction.alpha_eq status1 metasenv subst ctx term1 term2 then
        true
    else
        false
;;

let assume name ty eqty =
    distribute_tac (fun status goal ->
        match extract_conclusion_type status goal with
        | NCic.Prod (_,t,_) -> 
            if same_type_as_conclusion ty t status goal then
                match eqty with
                | None -> 
                        let (_,_,ty) = ty in
                        exec (exact_tac ("",0,(Ast.Binder (`Lambda,(Ast.Ident (name,None),Some ty),Ast.Implicit
                        `JustOne)))) status goal

                | Some eqty -> 
                    if same_type ty eqty status goal then
                    let (_,_,eqty) = eqty in
                        exec (exact_tac ("",0,(Ast.Binder (`Lambda,(Ast.Ident (name,None),Some eqty),Ast.Implicit
                        `JustOne)))) status goal
                    else
                        fail (lazy "The two given types are not equivalent")
            else
                fail (lazy "The assumed type is wrong")
        | _ -> fail (lazy "You can't assume without an universal quantification")
    )
;;

let suppose t1 id t2 =
    distribute_tac (fun status goal ->
        match extract_conclusion_type status goal with
        | NCic.Prod (_,t,_) -> 
            if same_type_as_conclusion t1 t status goal then
                match t2 with
                | None -> 
                        let (_,_,t1) = t1 in
                        exec (exact_tac ("",0,(Ast.Binder (`Lambda,(Ast.Ident (id,None),Some t1),Ast.Implicit
                        `JustOne)))) status goal

                | Some t2 -> 
                    if same_type t1 t2 status goal then
                    let (_,_,t2) = t2 in
                        exec (exact_tac ("",0,(Ast.Binder (`Lambda,(Ast.Ident (id,None),Some t2),Ast.Implicit
                        `JustOne)))) status goal
                    else
                        fail (lazy "The two given proposition are not equivalent")
            else
                fail (lazy "The supposed proposition is different from the premise")
        | _ -> fail (lazy "You can't suppose without a logical implication")
    )

let we_need_to_prove t id t1 =
    distribute_tac (fun status goal ->
        match id with
        | None -> 
            (
                match t1 with
                (* Change the conclusion of the sequent with t *)
                (* Is the pattern correct? Probably not *)
                | None ->  (* We need to prove t *)
                    exec (change_tac ~where:("",0,(None,[],Some Ast.UserInput)) ~with_what:t) status goal
                | Some t1 -> (* We need to prove t or equivalently t1 *)
                    if same_type t1 t status goal then
                        exec (change_tac ~where:("",0,(None,[],Some Ast.UserInput)) ~with_what:t1) status goal
                    else
                        fail (lazy "The two conclusions are not equivalent")
            )
        | Some id -> 
            (
                let (_,_,npt_t) = t in
                match t1 with
                | None -> (* We need to prove t (id) *)
                    exec (block_tac [cut_tac t; exact_tac ("",0,(Ast.LetIn ((Ast.Ident
                    (id,None),None),npt_t,Ast.Implicit
                    `JustOne)))]) status goal
                | Some t1 -> (* We need to prove t (id) or equivalently t1 *)
                    exec (block_tac [cut_tac t; change_tac ~where:("",0,(None,[],Some Ast.UserInput))
                    ~with_what:t1; exact_tac ("",0,(Ast.LetIn ((Ast.Ident (id,None),None),npt_t,Ast.Implicit
                    `JustOne)))]) status goal
            )
    )
;;

let by_just_we_proved just ty id ty' = 
    let just = mk_just just in
        match id with
        | None ->
            (match ty' with
                 | None -> (* just we proved P done *)
                     just 
                 | Some ty' -> (* just we proved P that is equivalent to P' done *)
                    (* I should probably check that ty' is the same thing as the conclusion of the
                    sequent of the open goal and that ty and ty' are equivalent *)
                     block_tac [ change_tac ~where:("",0,(None,[],Some Ast.UserInput)) ~with_what:ty; just]
             )
        | Some id ->
            let ty',continuation =
                match ty' with
                    | None -> ty,just
                    | Some ty' -> ty', block_tac [change_tac ~where:("",0,(None,[id,Ast.Implicit `JustOne],None))
                    ~with_what:ty; just] 
            in block_tac [cut_tac ty'; continuation ]
;;

let bydone just =
    mk_just just
;;

(*
let existselim just id1 t1 t2 id2 =
 let aux (proof, goal) = 
  let (n,metasenv,_subst,bo,ty,attrs) = proof in
  let metano,context,_ = CicUtil.lookup_meta goal metasenv in
  let t2, metasenv, _ = t2 (Some (Cic.Name id1, Cic.Decl t1) :: context) metasenv CicUniv.oblivion_ugraph in
  let proof' = (n,metasenv,_subst,bo,ty,attrs) in
   ProofEngineTypes.apply_tactic (
   Tacticals.thens
    ~start:(Tactics.cut (Cic.Appl [Cic.MutInd (UriManager.uri_of_string "cic:/matita/logic/connectives/ex.ind", 0, []); t1 ; Cic.Lambda (Cic.Name id1, t1, t2)]))
    ~continuations:
     [ Tactics.elim_intros (Cic.Rel 1)
        ~mk_fresh_name_callback:
          (let i = ref 0 in
            fun _ _ _  ~typ ->
             incr i;
             if !i = 1 then Cic.Name id1 else Cic.Name id2) ;
       (mk_just ~dbd ~automation_cache just)
     ]) (proof', goal)
 in
  ProofEngineTypes.mk_tactic aux
;;

let andelim just t1 id1 t2 id2 = 
   Tacticals.thens
    ~start:(Tactics.cut (Cic.Appl [Cic.MutInd (UriManager.uri_of_string "cic:/matita/logic/connectives/And.ind", 0, []); t1 ; t2]))
    ~continuations:
     [ Tactics.elim_intros (Cic.Rel 1)
        ~mk_fresh_name_callback:
          (let i = ref 0 in
            fun _ _ _  ~typ ->
             incr i;
             if !i = 1 then Cic.Name id1 else Cic.Name id2) ;
       (mk_just ~dbd ~automation_cache just) ]
;;
        *)
