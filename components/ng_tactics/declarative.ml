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

type just = [ `Term of NTacStatus.tactic_term | `Auto of NnAuto.auto_params ]

let mk_just =
    function
          `Auto (l,params) -> distribute_tac (fun status goal -> NnAuto.auto_lowtac
          ~params:(l,params) status goal)
        | `Term t -> apply_tac t

exception NotAProduct
exception FirstTypeWrong
exception NotEquivalentTypes

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
        if same_type_as_conclusion t1 t status goal then
            match t2 with
            | None -> 
                    let (_,_,t1) = t1 in
                    exec (exact_tac ("",0,(Ast.Binder (`Lambda,(Ast.Ident (id,None),Some t1),Ast.Implicit
                    `JustOne)))) status goal

            | Some t2 -> 
                let status,res = are_convertible t1 t2 status goal in
                if res then
                let (_,_,t2) = t2 in
                    exec (exact_tac ("",0,(Ast.Binder (`Lambda,(Ast.Ident (id,None),Some t2),Ast.Implicit
                    `JustOne)))) status goal
                else
                    raise NotEquivalentTypes
        else
            raise FirstTypeWrong
    | _ -> raise NotAProduct

let assume name ty eqty =
    distribute_tac (fun status goal ->
        try lambda_abstract_tac name ty eqty status goal
        with
        | NotAProduct -> fail (lazy "You can't assume without an universal quantification")
        | FirstTypeWrong ->  fail (lazy "The assumed type is wrong")
        | NotEquivalentTypes -> fail (lazy "The two given types are not equivalent")
     )
;;

let suppose t1 id t2 =
    distribute_tac (fun status goal ->
        try lambda_abstract_tac id t1 t2 status goal
        with
        | NotAProduct -> fail (lazy "You can't suppose without a logical implication")
        | FirstTypeWrong ->  fail (lazy "The supposed proposition is different from the premise")
        | NotEquivalentTypes -> fail (lazy "The two given propositions are not equivalent")
     )
;;

let assert_tac t1 t2 status goal continuation =
    let t = extract_conclusion_type status goal in
    if same_type_as_conclusion t1 t status goal then
        match t2 with
        | None -> exec continuation status goal
        | Some t2 ->
            let status,res = are_convertible t1 t2 status goal in
            if res then
                exec continuation status goal
            else
                raise NotEquivalentTypes
    else
        raise FirstTypeWrong

let we_need_to_prove t id t1 =
    distribute_tac (fun status goal ->
        match id with
        | None -> 
            (
                match t1 with
                | None ->  (* We need to prove t *)
                    (
                    try
                        assert_tac t None status goal id_tac
                    with
                    | FirstTypeWrong -> fail (lazy "The given proposition is not the same as the conclusion")
                    )
                | Some t1 -> (* We need to prove t or equivalently t1 *)
                    (
                        try
                            assert_tac t (Some t1) status goal (change_tac ~where:("",0,(None,[],Some Ast.UserInput)) ~with_what:t1)
                        with
                        | FirstTypeWrong -> fail (lazy "The given proposition is not the same as the conclusion")
                        | NotEquivalentTypes -> fail (lazy "The given propositions are not equivalent")
                    )
            )
        | Some id -> 
            (
                match t1 with
                | None -> (* We need to prove t (id) *)
                    exec (block_tac [cut_tac t; branch_tac ~force:false; shift_tac; intro_tac id;
                    (*merge_tac*)]) status goal
                | Some t1 -> (* We need to prove t (id) or equivalently t1 *)
                    exec (block_tac [cut_tac t; branch_tac ~force:false; change_tac ~where:("",0,(None,[],Some Ast.UserInput))
                    ~with_what:t1; shift_tac; intro_tac id; merge_tac]) status goal
            )
    )
;;

let by_just_we_proved just ty id ty' = 
    distribute_tac (fun status goal -> 
        let just = mk_just just in
            match id with
            | None ->
                (match ty' with
                     | None -> (* just we proved P done *)
                        (
                            try
                                assert_tac ty None status goal just
                            with
                            | FirstTypeWrong -> fail (lazy "The given proposition is not the same as the conclusion")
                            | NotEquivalentTypes -> fail (lazy "The given propositions are not equivalent")
                        )
                     | Some ty' -> (* just we proved P that is equivalent to P' done *)
                        (
                            try
                                assert_tac ty' (Some ty) status goal (block_tac [change_tac
                                ~where:("",0,(None,[],Some Ast.UserInput)) ~with_what:ty; just])
                            with
                            | FirstTypeWrong -> fail (lazy "The second proposition is not the same as the conclusion")
                            | NotEquivalentTypes -> fail (lazy "The given propositions are not equivalent")
                        )
                 )
            | Some id ->
                (
                    match ty' with
                    | None -> exec (block_tac [cut_tac ty; branch_tac; just; shift_tac; intro_tac
                    id; merge_tac ]) status goal
                    | Some ty' -> exec (block_tac [cut_tac ty; branch_tac; just; shift_tac; intro_tac
                    id; change_tac ~where:("",0,(None,[id,Ast.UserInput],None))
                    ~with_what:ty'; merge_tac]) status goal
                )
    )
;;

let thesisbecomes t1 t2 = we_need_to_prove t1 None t2 ;;

let bydone just =
    mk_just just
;;

let existselim just id1 t1 t2 id2 =
    let (_,_,t1) = t1 in
    let (_,_,t2) = t2 in
    let just = mk_just just in
    block_tac [
        cut_tac ("",0,(Ast.Appl [Ast.Ident ("ex",None); t1; Ast.Binder (`Lambda,(Ast.Ident
        (id1,None), Some t1),t2)])); 
        branch_tac ~force:false;
        just; 
        shift_tac; 
        case1_tac "_";
        intros_tac ~names_ref:(ref []) [id1;id2]; 
        merge_tac
    ]

let andelim just t1 id1 t2 id2 = 
    let (_,_,t1) = t1 in
    let (_,_,t2) = t2 in
    let just = mk_just just in
    block_tac [
        cut_tac ("",0,(Ast.Appl [Ast.Ident ("And",None); t1 ; t2])); 
        branch_tac ~force:false;
        just; 
        shift_tac; 
        case1_tac "_";
        intros_tac ~names_ref:(ref []) [id1;id2]; 
        merge_tac
    ]
;;



let rewritingstep lhs rhs just last_step = fail (lazy "Not implemented");
 (*
 let aux ((proof,goal) as status) =
  let (curi,metasenv,_subst,proofbo,proofty, attrs) = proof in
  let _,context,gty = CicUtil.lookup_meta goal metasenv in
  let eq,trans =
   match LibraryObjects.eq_URI () with
      None -> raise (ProofEngineTypes.Fail (lazy "You need to register the default equality first. Please use the \"default\" command"))
    | Some uri ->
      Cic.MutInd (uri,0,[]), Cic.Const (LibraryObjects.trans_eq_URI ~eq:uri,[])
  in
  let ty,_ =
   CicTypeChecker.type_of_aux' metasenv context rhs CicUniv.oblivion_ugraph in
  let just' =
   match just with
      `Auto (univ, params) ->
        let params =
         if not (List.exists (fun (k,_) -> k = "timeout") params) then
          ("timeout","3")::params
         else params
        in
        let params' =
         if not (List.exists (fun (k,_) -> k = "paramodulation") params) then
          ("paramodulation","1")::params
         else params
        in
         if params = params' then
          Tactics.auto ~dbd ~params:(univ, params) ~automation_cache
         else
          Tacticals.first
           [Tactics.auto ~dbd ~params:(univ, params) ~automation_cache ;
            Tactics.auto ~dbd ~params:(univ, params') ~automation_cache]
    | `Term just -> Tactics.apply just
    | `SolveWith term -> 
                    Tactics.demodulate ~automation_cache ~dbd
                    ~params:(Some [term],
                      ["all","1";"steps","1"; "use_context","false"])
    | `Proof ->
        Tacticals.id_tac
  in
   let plhs,prhs,prepare =
    match lhs with
       None ->
        let plhs,prhs =
         match gty with 
            Cic.Appl [_;_;plhs;prhs] -> plhs,prhs
          | _ -> assert false
        in
         plhs,prhs,
          (fun continuation ->
            ProofEngineTypes.apply_tactic continuation status)
     | Some (None,lhs) ->
        let plhs,prhs =
         match gty with 
            Cic.Appl [_;_;plhs;prhs] -> plhs,prhs
          | _ -> assert false
        in
         (*CSC: manca check plhs convertibile con lhs *)
         plhs,prhs,
          (fun continuation ->
            ProofEngineTypes.apply_tactic continuation status)
     | Some (Some name,lhs) ->
        let newmeta = CicMkImplicit.new_meta metasenv [] in
        let irl =
         CicMkImplicit.identity_relocation_list_for_metavariable context in
        let plhs = lhs in
        let prhs = Cic.Meta(newmeta,irl) in
         plhs,prhs,
          (fun continuation ->
            let metasenv = (newmeta, context, ty)::metasenv in
            let mk_fresh_name_callback =
             fun metasenv context _ ~typ ->
	      FreshNamesGenerator.mk_fresh_name ~subst:[] metasenv context
               (Cic.Name name) ~typ
	    in
            let proof = curi,metasenv,_subst,proofbo,proofty, attrs in
            let proof,goals =
             ProofEngineTypes.apply_tactic
              (Tacticals.thens
                ~start:(Tactics.cut ~mk_fresh_name_callback
                 (Cic.Appl [eq ; ty ; lhs ; prhs]))
                ~continuations:[Tacticals.id_tac ; continuation]) (proof,goal)
            in
             let goals =
              match just,goals with
                 `Proof, [g1;g2;g3] -> [g2;g3;newmeta;g1]
               | _, [g1;g2] -> [g2;newmeta;g1]
               | _, l -> 
                 prerr_endline (String.concat "," (List.map string_of_int l));
                 prerr_endline (CicMetaSubst.ppmetasenv [] metasenv);
                 assert false
             in
              proof,goals)
   in
    let continuation =
     if last_step then
      (*CSC:manca controllo sul fatto che rhs sia convertibile con prhs*)
      just'
     else
      Tacticals.thens
       ~start:(Tactics.apply ~term:(Cic.Appl [trans;ty;plhs;rhs;prhs]))
       ~continuations:[just' ; Tacticals.id_tac]
    in
     prepare continuation
 in
  ProofEngineTypes.mk_tactic aux
;;
  *)
