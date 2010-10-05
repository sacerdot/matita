(* Copyright (C) 2005, HELM Team.
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
 * http://helm.cs.unibo.it/
 *)

(* $Id$ *)

module PEH = ProofEngineHelpers

exception Drop
(* mo file name, ma file name *)
exception IncludedFileNotCompiled of string * string 
exception Macro of
 GrafiteAst.loc *
  (Cic.context -> GrafiteTypes.status * (Cic.term,Cic.lazy_term) GrafiteAst.macro)
exception NMacro of GrafiteAst.loc * GrafiteAst.nmacro

type 'a disambiguator_input = string * int * 'a

type options = { 
  do_heavy_checks: bool ; 
}

let concat_nuris uris nuris =
   match uris,nuris with
   | `New uris, `New nuris -> `New (nuris@uris)
   | _ -> assert false
;;
(** create a ProofEngineTypes.mk_fresh_name_type function which uses given
  * names as long as they are available, then it fallbacks to name generation
  * using FreshNamesGenerator module *)
let namer_of names =
  let len = List.length names in
  let count = ref 0 in
  fun metasenv context name ~typ ->
    if !count < len then begin
      let name = match List.nth names !count with
         | Some s -> Cic.Name s
	 | None   -> Cic.Anonymous
      in
      incr count;
      name
    end else
      FreshNamesGenerator.mk_fresh_name ~subst:[] metasenv context name ~typ

let rec tactic_of_ast status ast =
  let module PET = ProofEngineTypes in
  match ast with
  (* Higher order tactics *)
  | GrafiteAst.Do (loc, n, tactic) ->
     Tacticals.do_tactic n (tactic_of_ast status tactic)
  | GrafiteAst.Seq (loc, tactics) ->  (* tac1; tac2; ... *)
     Tacticals.seq (List.map (tactic_of_ast status) tactics)
  | GrafiteAst.Repeat (loc, tactic) ->
     Tacticals.repeat_tactic (tactic_of_ast status tactic)
  | GrafiteAst.Then (loc, tactic, tactics) ->  (* tac; [ tac1 | ... ] *)
     Tacticals.thens
      (tactic_of_ast status tactic)
      (List.map (tactic_of_ast status) tactics)
  | GrafiteAst.First (loc, tactics) ->
     Tacticals.first (List.map (tactic_of_ast status) tactics)
  | GrafiteAst.Try (loc, tactic) ->
     Tacticals.try_tactic (tactic_of_ast status tactic)
  | GrafiteAst.Solve (loc, tactics) ->
     Tacticals.solve_tactics (List.map (tactic_of_ast status) tactics)
  | GrafiteAst.Progress (loc, tactic) ->
     Tacticals.progress_tactic (tactic_of_ast status tactic)
  (* First order tactics *)
  | GrafiteAst.Absurd (_, term) -> Tactics.absurd term
  | GrafiteAst.Apply (_, term) -> Tactics.apply term
  | GrafiteAst.ApplyRule (_, term) -> Tactics.apply term
  | GrafiteAst.ApplyP (_, term) -> Tactics.applyP term
  | GrafiteAst.ApplyS (_, term, params) ->
     Tactics.applyS ~term ~params ~dbd:(LibraryDb.instance ())
       ~automation_cache:status#automation_cache
  | GrafiteAst.Assumption _ -> Tactics.assumption
  | GrafiteAst.AutoBatch (_,params) ->
      Tactics.auto ~params ~dbd:(LibraryDb.instance ()) 
	~automation_cache:status#automation_cache
  | GrafiteAst.Cases (_, what, pattern, (howmany, names)) ->
      Tactics.cases_intros ?howmany ~mk_fresh_name_callback:(namer_of names)
        ~pattern what
  | GrafiteAst.Change (_, pattern, with_what) ->
     Tactics.change ~pattern with_what
  | GrafiteAst.Clear (_,id) -> Tactics.clear id
  | GrafiteAst.ClearBody (_,id) -> Tactics.clearbody id
  | GrafiteAst.Compose (_,t1,t2,times,(howmany, names)) -> 
      Tactics.compose times t1 t2 ?howmany
        ~mk_fresh_name_callback:(namer_of names)
  | GrafiteAst.Contradiction _ -> Tactics.contradiction
  | GrafiteAst.Constructor (_, n) -> Tactics.constructor n
  | GrafiteAst.Cut (_, ident, term) ->
     let names = match ident with None -> [] | Some id -> [Some id] in
     Tactics.cut ~mk_fresh_name_callback:(namer_of names) term
  | GrafiteAst.Decompose (_, names) ->
      let mk_fresh_name_callback = namer_of names in
      Tactics.decompose ~mk_fresh_name_callback ()
  | GrafiteAst.Demodulate (_, params) -> 
      Tactics.demodulate 
	~dbd:(LibraryDb.instance ()) ~params 
          ~automation_cache:status#automation_cache
  | GrafiteAst.Destruct (_,xterms) -> Tactics.destruct xterms
  | GrafiteAst.Elim (_, what, using, pattern, (depth, names)) ->
      Tactics.elim_intros ?using ?depth ~mk_fresh_name_callback:(namer_of names)
        ~pattern what
  | GrafiteAst.ElimType (_, what, using, (depth, names)) ->
      Tactics.elim_type ?using ?depth ~mk_fresh_name_callback:(namer_of names)
        what
  | GrafiteAst.Exact (_, term) -> Tactics.exact term
  | GrafiteAst.Exists _ -> Tactics.exists
  | GrafiteAst.Fail _ -> Tactics.fail
  | GrafiteAst.Fold (_, reduction_kind, term, pattern) ->
      let reduction =
        match reduction_kind with
        | `Normalize ->
            PET.const_lazy_reduction
              (CicReduction.normalize ~delta:false ~subst:[])
        | `Simpl -> PET.const_lazy_reduction ProofEngineReduction.simpl
        | `Unfold None ->
            PET.const_lazy_reduction (ProofEngineReduction.unfold ?what:None)
        | `Unfold (Some lazy_term) ->
           (fun context metasenv ugraph ->
             let what, metasenv, ugraph = lazy_term context metasenv ugraph in
             ProofEngineReduction.unfold ~what, metasenv, ugraph)
        | `Whd ->
            PET.const_lazy_reduction (CicReduction.whd ~delta:false ~subst:[])
      in
      Tactics.fold ~reduction ~term ~pattern
  | GrafiteAst.Fourier _ -> Tactics.fourier
  | GrafiteAst.FwdSimpl (_, hyp, names) -> 
     Tactics.fwd_simpl ~mk_fresh_name_callback:(namer_of names)
      ~dbd:(LibraryDb.instance ()) hyp
  | GrafiteAst.Generalize (_,pattern,ident) ->
     let names = match ident with None -> [] | Some id -> [Some id] in
     Tactics.generalize ~mk_fresh_name_callback:(namer_of names) pattern 
  | GrafiteAst.IdTac _ -> Tactics.id
  | GrafiteAst.Intros (_, (howmany, names)) ->
      PrimitiveTactics.intros_tac ?howmany
        ~mk_fresh_name_callback:(namer_of names) ()
  | GrafiteAst.Inversion (_, term) ->
      Tactics.inversion term
  | GrafiteAst.LApply (_, linear, how_many, to_what, what, ident) ->
      let names = match ident with None -> [] | Some id -> [Some id] in
      Tactics.lapply ~mk_fresh_name_callback:(namer_of names) 
        ~linear ?how_many ~to_what what
  | GrafiteAst.Left _ -> Tactics.left
  | GrafiteAst.LetIn (loc,term,name) ->
      Tactics.letin term ~mk_fresh_name_callback:(namer_of [Some name])
  | GrafiteAst.Reduce (_, reduction_kind, pattern) ->
      (match reduction_kind with
	 | `Normalize -> Tactics.normalize ~pattern
	 | `Simpl -> Tactics.simpl ~pattern 
	 | `Unfold what -> Tactics.unfold ~pattern what
	 | `Whd -> Tactics.whd ~pattern)
  | GrafiteAst.Reflexivity _ -> Tactics.reflexivity
  | GrafiteAst.Replace (_, pattern, with_what) ->
     Tactics.replace ~pattern ~with_what
  | GrafiteAst.Rewrite (_, direction, t, pattern, names) ->
     EqualityTactics.rewrite_tac ~direction ~pattern t 
(* to be replaced with ~mk_fresh_name_callback:(namer_of names) *)
     (List.map (function Some s -> s | None -> assert false) names)
  | GrafiteAst.Right _ -> Tactics.right
  | GrafiteAst.Ring _ -> Tactics.ring
  | GrafiteAst.Split _ -> Tactics.split
  | GrafiteAst.Symmetry _ -> Tactics.symmetry
  | GrafiteAst.Transitivity (_, term) -> Tactics.transitivity term
  (* Implementazioni Aggiunte *)
  | GrafiteAst.Assume (_, id, t) -> Declarative.assume id t
  | GrafiteAst.Suppose (_, t, id, t1) -> Declarative.suppose t id t1
  | GrafiteAst.By_just_we_proved (_, just, ty, id, t1) ->
     Declarative.by_just_we_proved ~dbd:(LibraryDb.instance())
      ~automation_cache:status#automation_cache just ty id t1
  | GrafiteAst.We_need_to_prove (_, t, id, t2) ->
     Declarative.we_need_to_prove t id t2
  | GrafiteAst.Bydone (_, t) ->
     Declarative.bydone ~dbd:(LibraryDb.instance())
      ~automation_cache:status#automation_cache t
  | GrafiteAst.We_proceed_by_cases_on (_, t, t1) ->
     Declarative.we_proceed_by_cases_on t t1
  | GrafiteAst.We_proceed_by_induction_on (_, t, t1) ->
     Declarative.we_proceed_by_induction_on t t1
  | GrafiteAst.Byinduction (_, t, id) -> Declarative.byinduction t id
  | GrafiteAst.Thesisbecomes (_, t) -> Declarative.thesisbecomes t
  | GrafiteAst.ExistsElim (_, just, id1, t1, id2, t2) ->
     Declarative.existselim ~dbd:(LibraryDb.instance())
      ~automation_cache:status#automation_cache just id1 t1 id2 t2
  | GrafiteAst.Case (_,id,params) -> Declarative.case id params
  | GrafiteAst.AndElim(_,just,id1,t1,id2,t2) ->
     Declarative.andelim ~dbd:(LibraryDb.instance ())
      ~automation_cache:status#automation_cache just id1 t1 id2 t2
  | GrafiteAst.RewritingStep (_,termine,t1,t2,cont) ->
     Declarative.rewritingstep ~dbd:(LibraryDb.instance ())
      ~automation_cache:status#automation_cache termine t1 t2 cont

let classify_tactic tactic = 
  match tactic with
  (* tactics that can't close the goal (return a goal we want to "select") *)
  | GrafiteAst.Rewrite _ 
  | GrafiteAst.Split _ 
  | GrafiteAst.Replace _ 
  | GrafiteAst.Reduce _
  | GrafiteAst.IdTac _ 
  | GrafiteAst.Generalize _ 
  | GrafiteAst.Elim _ 
  | GrafiteAst.Cut _
  | GrafiteAst.Decompose _ -> true
  (* tactics like apply *)
  | _ -> false
  
let reorder_metasenv start refine tactic goals current_goal always_opens_a_goal=
(*   let print_m name metasenv =
    prerr_endline (">>>>> " ^ name);
    prerr_endline (CicMetaSubst.ppmetasenv [] metasenv)
  in *)
  (* phase one calculates:
   *   new_goals_from_refine:  goals added by refine
   *   head_goal:              the first goal opened by ythe tactic 
   *   other_goals:            other goals opened by the tactic
   *)
  let new_goals_from_refine = PEH.compare_metasenvs start refine in
  let new_goals_from_tactic = PEH.compare_metasenvs refine tactic in
  let head_goal, other_goals, goals = 
    match goals with
    | [] -> None,[],goals
    | hd::tl -> 
        (* assert (List.mem hd new_goals_from_tactic);
         * invalidato dalla goal_tac
         * *)
        Some hd, List.filter ((<>) hd) new_goals_from_tactic, List.filter ((<>)
        hd) goals
  in
  let produced_goals = 
    match head_goal with
    | None -> new_goals_from_refine @ other_goals
    | Some x -> x :: new_goals_from_refine @ other_goals
  in
  (* extract the metas generated by refine and tactic *)
  let metas_for_tactic_head = 
    match head_goal with
    | None -> []
    | Some head_goal -> List.filter (fun (n,_,_) -> n = head_goal) tactic in
  let metas_for_tactic_goals = 
    List.map 
      (fun x -> List.find (fun (metano,_,_) -> metano = x) tactic)
    goals 
  in
  let metas_for_refine_goals = 
    List.filter (fun (n,_,_) -> List.mem n new_goals_from_refine) tactic in
  let produced_metas, goals = 
    let produced_metas =
      if always_opens_a_goal then
        metas_for_tactic_head @ metas_for_refine_goals @ 
          metas_for_tactic_goals
      else begin
(*         print_m "metas_for_refine_goals" metas_for_refine_goals;
        print_m "metas_for_tactic_head" metas_for_tactic_head;
        print_m "metas_for_tactic_goals" metas_for_tactic_goals; *)
        metas_for_refine_goals @ metas_for_tactic_head @ 
          metas_for_tactic_goals
      end
    in
    let goals = List.map (fun (metano, _, _) -> metano)  produced_metas in
    produced_metas, goals
  in
  (* residual metas, preserving the original order *)
  let before, after = 
    let rec split e =
      function 
      | [] -> [],[]
      | (metano, _, _) :: tl when metano = e -> 
          [], List.map (fun (x,_,_) -> x) tl
      | (metano, _, _) :: tl -> let b, a = split e tl in metano :: b, a
    in
    let find n metasenv =
      try
        Some (List.find (fun (metano, _, _) -> metano = n) metasenv)
      with Not_found -> None
    in
    let extract l =
      List.fold_right 
        (fun n acc -> 
          match find n tactic with
          | Some x -> x::acc
          | None -> acc
        ) l [] in
    let before_l, after_l = split current_goal start in
    let before_l = 
      List.filter (fun x -> not (List.mem x produced_goals)) before_l in
    let after_l = 
      List.filter (fun x -> not (List.mem x produced_goals)) after_l in
    let before = extract before_l in
    let after = extract after_l in
      before, after
  in
(* |+   DEBUG CODE  +|
  print_m "BEGIN" start;
  prerr_endline ("goal was: " ^ string_of_int current_goal);
  prerr_endline ("and metas from refine are:");
  List.iter 
    (fun t -> prerr_string (" " ^ string_of_int t)) 
  new_goals_from_refine;
  prerr_endline "";
  print_m "before" before;
  print_m "metas_for_tactic_head" metas_for_tactic_head;
  print_m "metas_for_refine_goals" metas_for_refine_goals;
  print_m "metas_for_tactic_goals" metas_for_tactic_goals;
  print_m "produced_metas" produced_metas;
  print_m "after" after; 
|+   FINE DEBUG CODE +| *)
  before @ produced_metas @ after, goals 
  
let apply_tactic ~disambiguate_tactic (text,prefix_len,tactic) (status, goal) =
 let starting_metasenv = GrafiteTypes.get_proof_metasenv status in
 let before = List.map (fun g, _, _ -> g) starting_metasenv in
 let status, tactic = disambiguate_tactic status goal (text,prefix_len,tactic) in
 let metasenv_after_refinement =  GrafiteTypes.get_proof_metasenv status in
 let proof = GrafiteTypes.get_current_proof status in
 let proof_status = proof, goal in
 let always_opens_a_goal = classify_tactic tactic in
 let tactic = tactic_of_ast status tactic in
 let (proof, opened) = ProofEngineTypes.apply_tactic tactic proof_status in
 let after = ProofEngineTypes.goals_of_proof proof in
 let opened_goals, closed_goals = Tacticals.goals_diff ~before ~after ~opened in
 let proof, opened_goals = 
  let uri, metasenv_after_tactic, subst, t, ty, attrs = proof in
  let reordered_metasenv, opened_goals = 
    reorder_metasenv
     starting_metasenv
     metasenv_after_refinement metasenv_after_tactic
     opened goal always_opens_a_goal
  in
  let proof' = uri, reordered_metasenv, [], t, ty, attrs in
  proof', opened_goals
 in
 let incomplete_proof =
   match status#proof_status with
   | GrafiteTypes.Incomplete_proof p -> p
   | _ -> assert false
 in
  status#set_proof_status
   (GrafiteTypes.Incomplete_proof
     { incomplete_proof with GrafiteTypes.proof = proof }),
 opened_goals, closed_goals

let apply_atomic_tactical ~disambiguate_tactic ~patch (text,prefix_len,tactic) (status, goal) =
 let starting_metasenv = GrafiteTypes.get_proof_metasenv status in
 let before = List.map (fun g, _, _ -> g) starting_metasenv in
 let status, tactic = disambiguate_tactic status goal (text,prefix_len,tactic) in
 let metasenv_after_refinement =  GrafiteTypes.get_proof_metasenv status in
 let proof = GrafiteTypes.get_current_proof status in
 let proof_status = proof, goal in
 let always_opens_a_goal = classify_tactic tactic in
 let tactic = tactic_of_ast status tactic in
 let tactic = patch tactic in
 let (proof, opened) = ProofEngineTypes.apply_tactic tactic proof_status in
 let after = ProofEngineTypes.goals_of_proof proof in
 let opened_goals, closed_goals = Tacticals.goals_diff ~before ~after ~opened in
 let proof, opened_goals = 
  let uri, metasenv_after_tactic, _subst, t, ty, attrs = proof in
  let reordered_metasenv, opened_goals = 
    reorder_metasenv
     starting_metasenv
     metasenv_after_refinement metasenv_after_tactic
     opened goal always_opens_a_goal
  in
  let proof' = uri, reordered_metasenv, _subst, t, ty, attrs in
  proof', opened_goals
 in
 let incomplete_proof =
   match status#proof_status with
   | GrafiteTypes.Incomplete_proof p -> p
   | _ -> assert false
 in
  status#set_proof_status
   (GrafiteTypes.Incomplete_proof
     { incomplete_proof with GrafiteTypes.proof = proof }),
 opened_goals, closed_goals
type eval_ast =
 {ea_go:
  'term 'lazy_term 'reduction 'obj 'ident.
  disambiguate_tactic:
   (GrafiteTypes.status ->
    ProofEngineTypes.goal ->
    (('term, 'lazy_term, 'reduction, 'ident) GrafiteAst.tactic)
    disambiguator_input ->
    GrafiteTypes.status *
   (Cic.term, Cic.lazy_term, Cic.lazy_term GrafiteAst.reduction, string) GrafiteAst.tactic) ->

  disambiguate_command:
   (GrafiteTypes.status ->
    (('term,'obj) GrafiteAst.command) disambiguator_input ->
    GrafiteTypes.status * (Cic.term,Cic.obj) GrafiteAst.command) ->

  disambiguate_macro:
   (GrafiteTypes.status ->
    (('term,'lazy_term) GrafiteAst.macro) disambiguator_input ->
    Cic.context -> GrafiteTypes.status * (Cic.term,Cic.lazy_term) GrafiteAst.macro) ->

  ?do_heavy_checks:bool ->
  GrafiteTypes.status ->
  (('term, 'lazy_term, 'reduction, 'obj, 'ident) GrafiteAst.statement)
  disambiguator_input ->
  GrafiteTypes.status * [`Old of UriManager.uri list | `New of NUri.uri list]
 }

type 'a eval_command =
 {ec_go: 'term 'obj.
  disambiguate_command:
   (GrafiteTypes.status -> (('term,'obj) GrafiteAst.command) disambiguator_input ->
    GrafiteTypes.status * (Cic.term,Cic.obj) GrafiteAst.command) -> 
  options -> GrafiteTypes.status -> 
    (('term,'obj) GrafiteAst.command) disambiguator_input ->
   GrafiteTypes.status * [`Old of UriManager.uri list | `New of NUri.uri list]
 }

type 'a eval_comment =
 {ecm_go: 'term 'lazy_term 'reduction_kind 'obj 'ident.
  disambiguate_command:
   (GrafiteTypes.status -> (('term,'obj) GrafiteAst.command) disambiguator_input ->
    GrafiteTypes.status * (Cic.term,Cic.obj) GrafiteAst.command) -> 
  options -> GrafiteTypes.status -> 
    (('term,'lazy_term,'reduction_kind,'obj,'ident) GrafiteAst.comment) disambiguator_input ->
   GrafiteTypes.status * [`Old of UriManager.uri list | `New of NUri.uri list]
 }

type 'a eval_executable =
 {ee_go: 'term 'lazy_term 'reduction 'obj 'ident.
  disambiguate_tactic:
   (GrafiteTypes.status ->
    ProofEngineTypes.goal ->
    (('term, 'lazy_term, 'reduction, 'ident) GrafiteAst.tactic)
    disambiguator_input ->
    GrafiteTypes.status *
   (Cic.term, Cic.lazy_term, Cic.lazy_term GrafiteAst.reduction, string) GrafiteAst.tactic) ->

  disambiguate_command:
   (GrafiteTypes.status ->
    (('term,'obj) GrafiteAst.command) disambiguator_input ->
    GrafiteTypes.status * (Cic.term,Cic.obj) GrafiteAst.command) ->

  disambiguate_macro:
   (GrafiteTypes.status ->
    (('term,'lazy_term) GrafiteAst.macro) disambiguator_input ->
    Cic.context -> GrafiteTypes.status * (Cic.term,Cic.lazy_term) GrafiteAst.macro) ->

  options ->
  GrafiteTypes.status ->
  (('term, 'lazy_term, 'reduction, 'obj, 'ident) GrafiteAst.code) disambiguator_input ->
  GrafiteTypes.status * [`Old of UriManager.uri list | `New of NUri.uri list]
 }

type 'a eval_from_moo =
 { efm_go: GrafiteTypes.status -> string -> GrafiteTypes.status }
      
let coercion_moo_statement_of (uri,arity, saturations,_) =
  GrafiteAst.Coercion
   (HExtlib.dummy_floc, CicUtil.term_of_uri uri, false, arity, saturations)

let basic_eval_unification_hint (t,n) status =
 NCicUnifHint.add_user_provided_hint status t n
;;

let inject_unification_hint =
 let basic_eval_unification_hint (t,n) 
   ~refresh_uri_in_universe 
   ~refresh_uri_in_term
 =
  let t = refresh_uri_in_term t in basic_eval_unification_hint (t,n)
 in
  NCicLibrary.Serializer.register#run "unification_hints"
   object(_ : 'a NCicLibrary.register_type)
     method run = basic_eval_unification_hint
   end
;;

let eval_unification_hint status t n = 
 let metasenv,subst,status,t =
  GrafiteDisambiguate.disambiguate_nterm None status [] [] [] ("",0,t) in
 assert (metasenv=[]);
 let t = NCicUntrusted.apply_subst subst [] t in
 let status = basic_eval_unification_hint (t,n) status in
 let dump = inject_unification_hint (t,n)::status#dump in
 let status = status#set_dump dump in
  status,`New []
;;

let basic_index_obj l status =
  status#set_auto_cache 
    (List.fold_left
      (fun t (ks,v) -> 
         List.fold_left (fun t k ->
           NDiscriminationTree.DiscriminationTree.index t k v)
          t ks) 
    status#auto_cache l) 
;;     

let record_index_obj = 
 let aux l 
   ~refresh_uri_in_universe 
   ~refresh_uri_in_term
 =
    basic_index_obj
      (List.map 
        (fun ks,v -> List.map refresh_uri_in_term ks, refresh_uri_in_term v) 
      l)
 in
  NCicLibrary.Serializer.register#run "index_obj"
   object(_ : 'a NCicLibrary.register_type)
     method run = aux
   end
;;

let compute_keys status uri height kind = 
 let mk_item ty spec =
   let orig_ty = NTacStatus.mk_cic_term [] ty in
   let status,keys = NnAuto.keys_of_type status orig_ty in
   let keys =  
     List.map 
       (fun t -> 
	  snd (NTacStatus.term_of_cic_term status t (NTacStatus.ctx_of t)))
       keys
   in
   keys,NCic.Const(NReference.reference_of_spec uri spec)
 in
 let data = 
  match kind with
  | NCic.Fixpoint (ind,ifl,_) -> 
     HExtlib.list_mapi 
       (fun (_,_,rno,ty,_) i -> 
          if ind then mk_item ty (NReference.Fix (i,rno,height)) 
          else mk_item ty (NReference.CoFix height)) ifl
  | NCic.Inductive (b,lno,itl,_) -> 
     HExtlib.list_mapi 
       (fun (_,_,ty,_) i -> mk_item ty (NReference.Ind (b,i,lno))) itl 
     @
     List.map (fun ((_,_,ty),i,j) -> mk_item ty (NReference.Con (i,j+1,lno)))
       (List.flatten (HExtlib.list_mapi 
         (fun (_,_,_,cl) i -> HExtlib.list_mapi (fun x j-> x,i,j) cl)
         itl))
  | NCic.Constant (_,_,Some _, ty, _) -> 
     [ mk_item ty (NReference.Def height) ]
  | NCic.Constant (_,_,None, ty, _) ->
     [ mk_item ty NReference.Decl ]
 in
  HExtlib.filter_map
   (fun (keys, t) ->
     let keys = List.filter
       (function 
         | (NCic.Meta _) 
         | (NCic.Appl (NCic.Meta _::_)) -> false 
         | _ -> true) 
       keys
     in
     if keys <> [] then 
      begin
        HLog.debug ("Indexing:" ^ 
          NCicPp.ppterm ~metasenv:[] ~subst:[] ~context:[] t);
        HLog.debug ("With keys:" ^ String.concat "\n" (List.map (fun t ->
          NCicPp.ppterm ~metasenv:[] ~subst:[] ~context:[] t) keys));
        Some (keys,t) 
      end
     else 
      begin
        HLog.debug ("Not indexing:" ^ 
          NCicPp.ppterm ~metasenv:[] ~subst:[] ~context:[] t);
        None
      end)
    data
;;

let index_obj_for_auto status (uri, height, _, _, kind) = 
 (*prerr_endline (string_of_int height);*)
  let data = compute_keys status uri height kind in
  let status = basic_index_obj data status in
  let dump = record_index_obj data :: status#dump in   
  status#set_dump dump
;; 

let index_eq uri status =
  let eq_status = status#eq_cache in
  let eq_status1 = NCicParamod.index_obj eq_status uri in
    status#set_eq_cache eq_status1
;;

let record_index_eq =
 let basic_index_eq uri
   ~refresh_uri_in_universe 
   ~refresh_uri_in_term 
   = index_eq (NCicLibrary.refresh_uri uri) 
 in
  NCicLibrary.Serializer.register#run "index_eq"
   object(_ : 'a NCicLibrary.register_type)
     method run = basic_index_eq
   end
;;

let index_eq_for_auto status uri =
 if NnAuto.is_a_fact_obj status uri then
   let newstatus = index_eq uri status in
     if newstatus#eq_cache == status#eq_cache then status 
     else
       ((*prerr_endline ("recording " ^ (NUri.string_of_uri uri));*)
	let dump = record_index_eq uri :: newstatus#dump 
	in newstatus#set_dump dump)
 else 
   ((*prerr_endline "Not a fact";*)
   status)
;; 

let basic_eval_add_constraint (u1,u2) status =
 NCicLibrary.add_constraint status u1 u2
;;

let inject_constraint =
 let basic_eval_add_constraint (u1,u2) 
       ~refresh_uri_in_universe 
       ~refresh_uri_in_term
 =
  let u1 = refresh_uri_in_universe u1 in 
  let u2 = refresh_uri_in_universe u2 in 
  basic_eval_add_constraint (u1,u2)
 in
  NCicLibrary.Serializer.register#run "constraints"
   object(_:'a NCicLibrary.register_type)
     method run = basic_eval_add_constraint 
   end
;;

let eval_add_constraint status u1 u2 = 
 let status = basic_eval_add_constraint (u1,u2) status in
 let dump = inject_constraint (u1,u2)::status#dump in
 let status = status#set_dump dump in
  status,`Old []
;;

let add_coercions_of_lemmas lemmas status =
  let moo_content = 
    HExtlib.filter_map 
      (fun uri ->
        match CoercDb.is_a_coercion (Cic.Const (uri,[])) with
        | None -> None
        | Some (_,tgt,_,sat,_) ->
            let arity = match tgt with CoercDb.Fun n -> n | _ -> 0 in
            Some (coercion_moo_statement_of (uri,arity,sat,0)))
      lemmas
  in
  let status = GrafiteTypes.add_moo_content moo_content status in 
   status#set_coercions (CoercDb.dump ()), 
  lemmas

let eval_coercion status ~add_composites uri arity saturations =
 let uri = 
   try CicUtil.uri_of_term uri 
   with Invalid_argument _ -> 
     raise (Invalid_argument "coercion can only be constants/constructors")
 in
 let status, lemmas =
  GrafiteSync.add_coercion ~add_composites 
    ~pack_coercion_obj:CicRefine.pack_coercion_obj
   status uri arity saturations status#baseuri in
 let moo_content = coercion_moo_statement_of (uri,arity,saturations,0) in
 let status = GrafiteTypes.add_moo_content [moo_content] status in 
  add_coercions_of_lemmas lemmas status

let eval_prefer_coercion status c =
 let uri = 
   try CicUtil.uri_of_term c 
   with Invalid_argument _ -> 
     raise (Invalid_argument "coercion can only be constants/constructors")
 in
 let status = GrafiteSync.prefer_coercion status uri in
 let moo_content = GrafiteAst.PreferCoercion (HExtlib.dummy_floc,c) in
 let status = GrafiteTypes.add_moo_content [moo_content] status in 
 status, `Old []

module MatitaStatus =
 struct
  type input_status = GrafiteTypes.status * ProofEngineTypes.goal

  type output_status =
    GrafiteTypes.status * ProofEngineTypes.goal list * ProofEngineTypes.goal list

  type tactic = input_status -> output_status

  let mk_tactic tac = tac
  let apply_tactic tac = tac
  let goals (_, opened, closed) = opened, closed
  let get_stack (status, _) = GrafiteTypes.get_stack status
  
  let set_stack stack (status, opened, closed) = 
    GrafiteTypes.set_stack stack status, opened, closed

  let inject (status, _) = (status, [], [])
  let focus goal (status, _, _) = (status, goal)
 end

module MatitaTacticals = Continuationals.Make(MatitaStatus)

let tactic_of_ast' tac =
 MatitaTacticals.Tactical (MatitaTacticals.Tactic (MatitaStatus.mk_tactic tac))

let punctuation_tactical_of_ast (text,prefix_len,punct) =
 match punct with
  | GrafiteAst.Dot _loc -> MatitaTacticals.Dot
  | GrafiteAst.Semicolon _loc -> MatitaTacticals.Semicolon
  | GrafiteAst.Branch _loc -> MatitaTacticals.Branch
  | GrafiteAst.Shift _loc -> MatitaTacticals.Shift
  | GrafiteAst.Pos (_loc, i) -> MatitaTacticals.Pos i
  | GrafiteAst.Merge _loc -> MatitaTacticals.Merge
  | GrafiteAst.Wildcard _loc -> MatitaTacticals.Wildcard

let non_punctuation_tactical_of_ast (text,prefix_len,punct) =
 match punct with
  | GrafiteAst.Focus (_loc,goals) -> MatitaTacticals.Focus goals
  | GrafiteAst.Unfocus _loc -> MatitaTacticals.Unfocus
  | GrafiteAst.Skip _loc -> MatitaTacticals.Tactical MatitaTacticals.Skip

let eval_tactical status tac =
  let status, _, _ = MatitaTacticals.eval tac (status, ~-1) in
  let status =  (* is proof completed? *)
    match status#proof_status with
    | GrafiteTypes.Incomplete_proof
       { GrafiteTypes.stack = stack; proof = proof }
      when Continuationals.Stack.is_empty stack ->
       status#set_proof_status (GrafiteTypes.Proof proof)
    | _ -> status
  in
  status

let add_obj = GrafiteSync.add_obj ~pack_coercion_obj:CicRefine.pack_coercion_obj

let eval_ng_punct (_text, _prefix_len, punct) =
  match punct with
  | GrafiteAst.Dot _ -> NTactics.dot_tac 
  | GrafiteAst.Semicolon _ -> fun x -> x
  | GrafiteAst.Branch _ -> NTactics.branch_tac ~force:false
  | GrafiteAst.Shift _ -> NTactics.shift_tac 
  | GrafiteAst.Pos (_,l) -> NTactics.pos_tac l
  | GrafiteAst.Wildcard _ -> NTactics.wildcard_tac 
  | GrafiteAst.Merge _ -> NTactics.merge_tac 
;;

let eval_ng_tac tac =
 let rec aux f (text, prefix_len, tac) =
  match tac with
  | GrafiteAst.NApply (_loc, t) -> NTactics.apply_tac (text,prefix_len,t) 
  | GrafiteAst.NSmartApply (_loc, t) -> 
      NnAuto.smart_apply_tac (text,prefix_len,t) 
  | GrafiteAst.NAssert (_loc, seqs) ->
     NTactics.assert_tac
      ((List.map
        (function (hyps,concl) ->
          List.map
           (function
              (id,`Decl t) -> id,`Decl (text,prefix_len,t)
             |(id,`Def (b,t))->id,`Def((text,prefix_len,b),(text,prefix_len,t))
           ) hyps,
          (text,prefix_len,concl))
       ) seqs)
  | GrafiteAst.NAuto (_loc, (None,a)) -> 
      NAuto.auto_tac ~params:(None,a) ?trace_ref:None
  | GrafiteAst.NAuto (_loc, (Some l,a)) ->
      NAuto.auto_tac
	~params:(Some List.map (fun x -> "",0,x) l,a) ?trace_ref:None
  | GrafiteAst.NBranch _ -> NTactics.branch_tac ~force:false
  | GrafiteAst.NCases (_loc, what, where) ->
      NTactics.cases_tac 
        ~what:(text,prefix_len,what)
        ~where:(text,prefix_len,where)
  | GrafiteAst.NCase1 (_loc,n) -> NTactics.case1_tac n
  | GrafiteAst.NChange (_loc, pat, ww) -> 
      NTactics.change_tac 
       ~where:(text,prefix_len,pat) ~with_what:(text,prefix_len,ww) 
  | GrafiteAst.NConstructor (_loc,num,args) -> 
     NTactics.constructor_tac 
       ?num ~args:(List.map (fun x -> text,prefix_len,x) args)
  | GrafiteAst.NCut (_loc, t) -> NTactics.cut_tac (text,prefix_len,t) 
(*| GrafiteAst.NDiscriminate (_,what) -> NDestructTac.discriminate_tac ~what:(text,prefix_len,what)
  | GrafiteAst.NSubst (_,what) -> NDestructTac.subst_tac ~what:(text,prefix_len,what)*)
  | GrafiteAst.NDestruct (_,dom,skip) -> NDestructTac.destruct_tac dom skip
  | GrafiteAst.NDot _ -> NTactics.dot_tac 
  | GrafiteAst.NElim (_loc, what, where) ->
      NTactics.elim_tac 
        ~what:(text,prefix_len,what)
        ~where:(text,prefix_len,where)
  | GrafiteAst.NFocus (_,l) -> NTactics.focus_tac l
  | GrafiteAst.NGeneralize (_loc, where) -> 
      NTactics.generalize_tac ~where:(text,prefix_len,where)
  | GrafiteAst.NId _ -> (fun x -> x)
  | GrafiteAst.NIntro (_loc,n) -> NTactics.intro_tac n
  | GrafiteAst.NIntros (_loc,ns) -> NTactics.intros_tac ns
  | GrafiteAst.NInversion (_loc, what, where) ->
      NTactics.inversion_tac 
        ~what:(text,prefix_len,what)
        ~where:(text,prefix_len,where)
  | GrafiteAst.NLApply (_loc, t) -> NTactics.lapply_tac (text,prefix_len,t) 
  | GrafiteAst.NLetIn (_loc,where,what,name) ->
      NTactics.letin_tac ~where:(text,prefix_len,where) 
        ~what:(text,prefix_len,what) name
  | GrafiteAst.NMerge _ -> NTactics.merge_tac 
  | GrafiteAst.NPos (_,l) -> NTactics.pos_tac l
  | GrafiteAst.NPosbyname (_,s) -> NTactics.case_tac s
  | GrafiteAst.NReduce (_loc, reduction, where) ->
      NTactics.reduce_tac ~reduction ~where:(text,prefix_len,where)
  | GrafiteAst.NRewrite (_loc,dir,what,where) ->
     NTactics.rewrite_tac ~dir ~what:(text,prefix_len,what)
      ~where:(text,prefix_len,where)
  | GrafiteAst.NSemicolon _ -> fun x -> x
  | GrafiteAst.NShift _ -> NTactics.shift_tac 
  | GrafiteAst.NSkip _ -> NTactics.skip_tac
  | GrafiteAst.NUnfocus _ -> NTactics.unfocus_tac
  | GrafiteAst.NWildcard _ -> NTactics.wildcard_tac 
  | GrafiteAst.NTry (_,tac) -> NTactics.try_tac
      (aux f (text, prefix_len, tac))
  | GrafiteAst.NAssumption _ -> NTactics.assumption_tac
  | GrafiteAst.NBlock (_,l) -> 
      NTactics.block_tac (List.map (fun x -> aux f (text,prefix_len,x)) l)
  |GrafiteAst.NRepeat (_,tac) ->
      NTactics.repeat_tac (f f (text, prefix_len, tac))
 in
  aux aux tac (* trick for non uniform recursion call *)
;;
      
let subst_metasenv_and_fix_names status =
  let u,h,metasenv, subst,o = status#obj in
  let o = 
    NCicUntrusted.map_obj_kind ~skip_body:true 
     (NCicUntrusted.apply_subst subst []) o
  in
   status#set_obj(u,h,NCicUntrusted.apply_subst_metasenv subst metasenv,subst,o)
;;


let rec eval_ncommand opts status (text,prefix_len,cmd) =
  match cmd with
  | GrafiteAst.UnificationHint (loc, t, n) -> eval_unification_hint status t n
  | GrafiteAst.NCoercion (loc, name, t, ty, source, target) ->
      NCicCoercDeclaration.eval_ncoercion status name t ty source target
  | GrafiteAst.NQed loc ->
     if status#ng_mode <> `ProofMode then
      raise (GrafiteTypes.Command_error "Not in proof mode")
     else
      let uri,height,menv,subst,obj_kind = status#obj in
       if menv <> [] then
        raise
         (GrafiteTypes.Command_error"You can't Qed an incomplete theorem")
       else
        let obj_kind =
         NCicUntrusted.map_obj_kind 
          (NCicUntrusted.apply_subst subst []) obj_kind in
        let height = NCicTypeChecker.height_of_obj_kind uri [] obj_kind in
        (* fix the height inside the object *)
        let rec fix () = function 
          | NCic.Const (NReference.Ref (u,spec)) when NUri.eq u uri -> 
             NCic.Const (NReference.reference_of_spec u
              (match spec with
              | NReference.Def _ -> NReference.Def height
              | NReference.Fix (i,j,_) -> NReference.Fix(i,j,height)
              | NReference.CoFix _ -> NReference.CoFix height
              | NReference.Ind _ | NReference.Con _
              | NReference.Decl as s -> s))
          | t -> NCicUtils.map (fun _ () -> ()) () fix t
        in
        let obj_kind = 
          match obj_kind with
          | NCic.Fixpoint _ -> 
              NCicUntrusted.map_obj_kind (fix ()) obj_kind 
          | _ -> obj_kind
        in
        let obj = uri,height,[],[],obj_kind in
        prerr_endline ("pp new obj \n"^NCicPp.ppobj obj);
        let old_status = status in
        let status = NCicLibrary.add_obj status obj in
        let index_obj =
         match obj_kind with
            NCic.Constant (_,_,_,_,(_,`Example,_))
          | NCic.Fixpoint (_,_,(_,`Example,_)) -> false
          | _ -> true
        in
        let status =
         if index_obj then
          let status = index_obj_for_auto status obj in
           (try index_eq_for_auto status uri
           with _ -> status)
         else
          status in
(*
	  try 
	    index_eq uri status
	  with _ -> prerr_endline "got an exception"; status
	in *)
(*         prerr_endline (NCicPp.ppobj obj); *)
        HLog.message ("New object: " ^ NUri.string_of_uri uri);
         (try
       (*prerr_endline (NCicPp.ppobj obj);*)
           let boxml = NCicElim.mk_elims obj in
           let boxml = boxml @ NCicElim.mk_projections obj in
(*
           let objs = [] in
           let timestamp,uris_rev =
             List.fold_left
              (fun (status,uris_rev) (uri,_,_,_,_) as obj ->
                let status = NCicLibrary.add_obj status obj in
                 status,uri::uris_rev
              ) (status,[]) objs in
           let uris = uri::List.rev uris_rev in
*)
           let status = status#set_ng_mode `CommandMode in
           let status = LexiconSync.add_aliases_for_objs status (`New [uri]) in
           let status,uris =
            List.fold_left
             (fun (status,uris) boxml ->
               try
                let nstatus,nuris =
                 eval_ncommand opts status
                  ("",0,GrafiteAst.NObj (HExtlib.dummy_floc,boxml))
                in
                if nstatus#ng_mode <> `CommandMode then
                  begin
                    (*HLog.warn "error in generating projection/eliminator";*)
                    status, uris
                  end
                else
                  nstatus, concat_nuris uris nuris
               with
               | MultiPassDisambiguator.DisambiguationError _
               | NCicTypeChecker.TypeCheckerFailure _ ->
                  (*HLog.warn "error in generating projection/eliminator";*)
                  status,uris
             ) (status,`New [] (* uris *)) boxml in             
           let _,_,_,_,nobj = obj in 
           let status = match nobj with
               NCic.Inductive (is_ind,leftno,[it],_) ->
                 let _,ind_name,ty,cl = it in
                 List.fold_left 
                   (fun status outsort ->
                      let status = status#set_ng_mode `ProofMode in
                      try
                       (let status,invobj =
                         NInversion.mk_inverter 
                          (ind_name ^ "_inv_" ^
                            (snd (NCicElim.ast_of_sort outsort)))
                          is_ind it leftno outsort status status#baseuri in
                       let _,_,menv,_,_ = invobj in
                       fst (match menv with
                             [] -> eval_ncommand opts status ("",0,GrafiteAst.NQed Stdpp.dummy_loc)
                           | _ -> status,`New []))
                       (* XXX *)
                      with _ -> (*HLog.warn "error in generating inversion principle"; *)
                                let status = status#set_ng_mode `CommandMode in status)
                  status
                  (NCic.Prop::
                    List.map (fun s -> NCic.Type s) (NCicEnvironment.get_universes ()))
              | _ -> status
           in
           let coercions =
            match obj with
              _,_,_,_,NCic.Inductive
               (true,leftno,[_,_,_,[_,_,_]],(_,`Record fields))
               ->
                HExtlib.filter_map
                 (fun (name,is_coercion,arity) ->
                   if is_coercion then Some(name,leftno,arity) else None) fields
            | _ -> [] in
           let status,uris =
            List.fold_left
             (fun (status,uris) (name,cpos,arity) ->
               try
                 let metasenv,subst,status,t =
                  GrafiteDisambiguate.disambiguate_nterm None status [] [] []
                   ("",0,CicNotationPt.Ident (name,None)) in
                 assert (metasenv = [] && subst = []);
                 let status, nuris = 
                   NCicCoercDeclaration.
                     basic_eval_and_record_ncoercion_from_t_cpos_arity 
                      status (name,t,cpos,arity)
                 in
                 let uris = concat_nuris nuris uris in
                 status, uris
               with MultiPassDisambiguator.DisambiguationError _-> 
                 HLog.warn ("error in generating coercion: "^name);
                 status, uris) 
             (status,uris) coercions
           in
            status,uris
          with
           exn ->
            NCicLibrary.time_travel old_status;
            raise exn)
  | GrafiteAst.NCopy (log,tgt,src_uri, map) ->
     if status#ng_mode <> `CommandMode then
      raise (GrafiteTypes.Command_error "Not in command mode")
     else
       let tgt_uri_ext, old_ok = 
         match NCicEnvironment.get_checked_obj src_uri with
         | _,_,[],[], (NCic.Inductive _ as ok) -> ".ind", ok
         | _,_,[],[], (NCic.Fixpoint _ as ok) -> ".con", ok
         | _,_,[],[], (NCic.Constant _ as ok) -> ".con", ok
         | _ -> assert false
       in
       let tgt_uri = NUri.uri_of_string (status#baseuri^"/"^tgt^tgt_uri_ext) in
       let map = (src_uri, tgt_uri) :: map in
       let ok = 
         let rec subst () = function
           | NCic.Meta _ -> assert false
           | NCic.Const (NReference.Ref (u,spec)) as t ->
               (try NCic.Const 
                 (NReference.reference_of_spec (List.assoc u map)spec)
               with Not_found -> t)
           | t -> NCicUtils.map (fun _ _ -> ()) () subst t
         in
         NCicUntrusted.map_obj_kind ~skip_body:false (subst ()) old_ok
       in
       let ninitial_stack = Continuationals.Stack.of_nmetasenv [] in
       let status = status#set_obj (tgt_uri,0,[],[],ok) in
       (*prerr_endline (NCicPp.ppobj (tgt_uri,0,[],[],ok));*)
       let status = status#set_stack ninitial_stack in
       let status = subst_metasenv_and_fix_names status in
       let status = status#set_ng_mode `ProofMode in
       eval_ncommand opts status ("",0,GrafiteAst.NQed Stdpp.dummy_loc)
  | GrafiteAst.NObj (loc,obj) ->
     if status#ng_mode <> `CommandMode then
      raise (GrafiteTypes.Command_error "Not in command mode")
     else
      let status,obj =
       GrafiteDisambiguate.disambiguate_nobj status
        ~baseuri:status#baseuri (text,prefix_len,obj) in
      let uri,height,nmenv,nsubst,nobj = obj in
      let ninitial_stack = Continuationals.Stack.of_nmetasenv nmenv in
      let status = status#set_obj obj in
      let status = status#set_stack ninitial_stack in
      let status = subst_metasenv_and_fix_names status in
      let status = status#set_ng_mode `ProofMode in
      (match nmenv with
          [] ->
           eval_ncommand opts status ("",0,GrafiteAst.NQed Stdpp.dummy_loc)
        | _ -> status,`New [])
  | GrafiteAst.NDiscriminator (_,_) -> assert false (*(loc, indty) ->
      if status#ng_mode <> `CommandMode then
        raise (GrafiteTypes.Command_error "Not in command mode")
      else
        let status = status#set_ng_mode `ProofMode in
        let metasenv,subst,status,indty =
          GrafiteDisambiguate.disambiguate_nterm None status [] [] [] (text,prefix_len,indty) in
        let indtyno, (_,_,tys,_,_) = match indty with
            NCic.Const ((NReference.Ref (_,NReference.Ind (_,indtyno,_))) as r) ->
              indtyno, NCicEnvironment.get_checked_indtys r
          | _ -> prerr_endline ("engine: indty expected... (fix this error message)"); assert false in
        let it = List.nth tys indtyno in
        let status,obj =  NDestructTac.mk_discriminator it status in
        let _,_,menv,_,_ = obj in
          (match menv with
               [] -> eval_ncommand opts status ("",0,GrafiteAst.NQed Stdpp.dummy_loc)
             | _ -> prerr_endline ("Discriminator: non empty metasenv");
                    status, `New []) *)
  | GrafiteAst.NInverter (loc, name, indty, selection, sort) ->
     if status#ng_mode <> `CommandMode then
      raise (GrafiteTypes.Command_error "Not in command mode")
     else
      let metasenv,subst,status,sort = match sort with
        | None -> [],[],status,NCic.Sort NCic.Prop
        | Some s -> GrafiteDisambiguate.disambiguate_nterm None status [] [] []
                      (text,prefix_len,s) 
      in
      assert (metasenv = []);
      let sort = NCicReduction.whd ~subst [] sort in
      let sort = match sort with 
          NCic.Sort s -> s
        | _ ->  raise (Invalid_argument (Printf.sprintf "ninverter: found target %s, which is not a sort" 
                                           (NCicPp.ppterm ~metasenv ~subst ~context:[] sort)))
      in
      let status = status#set_ng_mode `ProofMode in
      let metasenv,subst,status,indty =
       GrafiteDisambiguate.disambiguate_nterm None status [] [] subst (text,prefix_len,indty) in
      let indtyno,(_,leftno,tys,_,_) = match indty with
          NCic.Const ((NReference.Ref (_,NReference.Ind (_,indtyno,_))) as r) -> 
            indtyno, NCicEnvironment.get_checked_indtys r
        | _ -> prerr_endline ("engine: indty ="  ^ NCicPp.ppterm ~metasenv:[] ~subst:[] ~context:[] indty) ; assert false in
      let it = List.nth tys indtyno in
     let status,obj = NInversion.mk_inverter name true it leftno ?selection sort 
                        status status#baseuri in
     let _,_,menv,_,_ = obj in
     (match menv with
        [] ->
          eval_ncommand opts status ("",0,GrafiteAst.NQed Stdpp.dummy_loc)
      | _ -> assert false)
  | GrafiteAst.NUnivConstraint (loc,u1,u2) ->
      eval_add_constraint status [`Type,u1] [`Type,u2]
;;

let rec eval_command = {ec_go = fun ~disambiguate_command opts status
(text,prefix_len,cmd) ->
 let status,cmd = disambiguate_command status (text,prefix_len,cmd) in
 let status,uris =
  match cmd with
  | GrafiteAst.Index (loc,None,uri) -> 
	assert false (* TODO: for user input *)
  | GrafiteAst.Index (loc,Some key,uri) -> 
      let universe = 
        status#automation_cache.AutomationCache.univ
      in
      let universe = Universe.index universe key (CicUtil.term_of_uri uri) in
      let cache = { 
        status#automation_cache with AutomationCache.univ = universe } 
      in
      let status = status#set_automation_cache cache in
(* debug
      let msg =
       let candidates = Universe.get_candidates status.GrafiteTypes.universe key in
       ("candidates for " ^ (CicPp.ppterm key) ^ " = " ^ 
	  (String.concat "\n" (List.map CicPp.ppterm candidates))) 
     in
     prerr_endline msg;
*)
      let status = GrafiteTypes.add_moo_content [cmd] status in
      status,`Old [] 
  | GrafiteAst.Select (_,uri) as cmd ->
      if List.mem cmd status#moo_content_rev then status, `Old []
      else 
       let cache = 
         AutomationCache.add_term_to_active status#automation_cache
           [] [] [] (CicUtil.term_of_uri uri) None
       in
       let status = status#set_automation_cache cache in
       let status = GrafiteTypes.add_moo_content [cmd] status in
       status, `Old []
  | GrafiteAst.Pump (_,steps) ->
      let cache = 
        AutomationCache.pump status#automation_cache steps
      in
      let status = status#set_automation_cache cache in
      status, `Old []
  | GrafiteAst.PreferCoercion (loc, coercion) ->
     eval_prefer_coercion status coercion
  | GrafiteAst.Coercion (loc, uri, add_composites, arity, saturations) ->
     let res,uris =
      eval_coercion status ~add_composites uri arity saturations
     in
      res,`Old uris
  | GrafiteAst.Inverter (loc, name, indty, params) ->
     let buri = status#baseuri in 
     let uri = UriManager.uri_of_string (buri ^ "/" ^ name ^ ".con") in
     let indty_uri = 
       try CicUtil.uri_of_term indty
       with Invalid_argument _ ->
         raise (Invalid_argument "not an inductive type to invert") in
     let res,uris =
      Inversion_principle.build_inverter ~add_obj status uri indty_uri params
     in
      res,`Old uris
  | GrafiteAst.Default (loc, what, uris) as cmd ->
     LibraryObjects.set_default what uris;
     GrafiteTypes.add_moo_content [cmd] status,`Old []
  | GrafiteAst.Drop loc -> raise Drop
  | GrafiteAst.Include (loc, mode, new_or_old, baseuri) ->
     (* Old Include command is not recursive; new one is *)
     let status =
      if new_or_old = `OldAndNew then
       let moopath_rw, moopath_r = 
        LibraryMisc.obj_file_of_baseuri 
          ~must_exist:false ~baseuri ~writable:true,
        LibraryMisc.obj_file_of_baseuri 
          ~must_exist:false ~baseuri ~writable:false in
       let moopath = 
        if Sys.file_exists moopath_r then moopath_r else
          if Sys.file_exists moopath_rw then moopath_rw else
            raise (IncludedFileNotCompiled (moopath_rw,baseuri))
       in
        eval_from_moo.efm_go status moopath
      else
       status
     in
      let status =
       NCicLibrary.Serializer.require ~baseuri:(NUri.uri_of_string baseuri)
        status in
      let status =
       GrafiteTypes.add_moo_content
        [GrafiteAst.Include (loc,mode,`New,baseuri)] status
      in
       status,`Old []
  | GrafiteAst.Print (_,"proofterm") ->
      let _,_,_,p,_, _ = GrafiteTypes.get_current_proof status in
      prerr_endline (Auto.pp_proofterm (Lazy.force p));
      status,`Old []
  | GrafiteAst.Print (_,_) -> status,`Old []
  | GrafiteAst.Qed loc ->
      let uri, metasenv, _subst, bo, ty, attrs =
        match status#proof_status with
        | GrafiteTypes.Proof (Some uri, metasenv, subst, body, ty, attrs) ->
            uri, metasenv, subst, body, ty, attrs
        | GrafiteTypes.Proof (None, metasenv, subst, body, ty, attrs) -> 
            raise (GrafiteTypes.Command_error 
              ("Someone allows to start a theorem without giving the "^
               "name/uri. This should be fixed!"))
        | _->
          raise
           (GrafiteTypes.Command_error "You can't Qed an incomplete theorem")
      in
      if metasenv <> [] then 
        raise
         (GrafiteTypes.Command_error
           "Proof not completed! metasenv is not empty!");
      let name = UriManager.name_of_uri uri in
      let obj = Cic.Constant (name,Some (Lazy.force bo),ty,[],attrs) in
      let status, lemmas = add_obj uri obj status in
       status#set_proof_status GrafiteTypes.No_proof,
        (*CSC: I throw away the arities *)
        `Old (uri::lemmas)
  | GrafiteAst.Relation (loc, id, a, aeq, refl, sym, trans) -> 
     Setoids.add_relation id a aeq refl sym trans;
     status, `Old [] (*CSC: TO BE FIXED *)
  | GrafiteAst.Set (loc, name, value) -> status, `Old []
(*       GrafiteTypes.set_option status name value,[] *)
  | GrafiteAst.Obj (loc,obj) -> (* MATITA 1.0 *) assert false
 in
  match status#proof_status with
     GrafiteTypes.Intermediate _ ->
      status#set_proof_status GrafiteTypes.No_proof,uris
   | _ -> status,uris

} and eval_executable = {ee_go = fun ~disambiguate_tactic ~disambiguate_command
~disambiguate_macro opts status (text,prefix_len,ex) ->
  match ex with
  | GrafiteAst.Tactic (_(*loc*), Some tac, punct) ->
     let tac = apply_tactic ~disambiguate_tactic (text,prefix_len,tac) in
     let status = eval_tactical status (tactic_of_ast' tac) in
     (* CALL auto on every goal, easy way of testing it  
     let auto = 
       GrafiteAst.AutoBatch 
         (loc, ([],["depth","2";"timeout","1";"type","1"])) in
     (try
       let auto = apply_tactic ~disambiguate_tactic ("",0,auto) in
       let _ = eval_tactical status (tactic_of_ast' auto) in 
       print_endline "GOOD"; () 
     with ProofEngineTypes.Fail _ -> print_endline "BAD" | _ -> ());*)
      eval_tactical status
       (punctuation_tactical_of_ast (text,prefix_len,punct)),`Old []
  | GrafiteAst.Tactic (_, None, punct) ->
      eval_tactical status
       (punctuation_tactical_of_ast (text,prefix_len,punct)),`Old []
  | GrafiteAst.NTactic (_(*loc*), tacl) ->
      if status#ng_mode <> `ProofMode then
       raise (GrafiteTypes.Command_error "Not in proof mode")
      else
       let status =
        List.fold_left 
          (fun status tac ->
            let status = eval_ng_tac (text,prefix_len,tac) status in
            subst_metasenv_and_fix_names status)
          status tacl
       in
        status,`New []
  | GrafiteAst.NonPunctuationTactical (_, tac, punct) ->
     let status = 
      eval_tactical status
       (non_punctuation_tactical_of_ast (text,prefix_len,tac))
     in
      eval_tactical status
       (punctuation_tactical_of_ast (text,prefix_len,punct)),`Old []
  | GrafiteAst.Command (_, cmd) ->
      eval_command.ec_go ~disambiguate_command opts status (text,prefix_len,cmd)
  | GrafiteAst.NCommand (_, cmd) ->
      eval_ncommand opts status (text,prefix_len,cmd)
  | GrafiteAst.Macro (loc, macro) ->
     raise (Macro (loc,disambiguate_macro status (text,prefix_len,macro)))
  | GrafiteAst.NMacro (loc, macro) ->
     raise (NMacro (loc,macro))

} and eval_from_moo = {efm_go = fun status fname ->
  let ast_of_cmd cmd =
    ("",0,GrafiteAst.Executable (HExtlib.dummy_floc,
      GrafiteAst.Command (HExtlib.dummy_floc,
        cmd)))
  in
  let moo = GrafiteMarshal.load_moo fname in
  List.fold_left 
    (fun status ast -> 
      let ast = ast_of_cmd ast in
      let status,lemmas =
       eval_ast.ea_go
         ~disambiguate_tactic:(fun status _ (_,_,tactic) -> status,tactic)
         ~disambiguate_command:(fun status (_,_,cmd) -> status,cmd)
         ~disambiguate_macro:(fun _ _ -> assert false)
         status ast
      in
       assert (lemmas=`Old []);
       status)
    status moo
} and eval_ast = {ea_go = fun ~disambiguate_tactic ~disambiguate_command
~disambiguate_macro ?(do_heavy_checks=false) status
(text,prefix_len,st)
->
  let opts = { do_heavy_checks = do_heavy_checks ; } in
  match st with
  | GrafiteAst.Executable (_,ex) ->
     eval_executable.ee_go ~disambiguate_tactic ~disambiguate_command
      ~disambiguate_macro opts status (text,prefix_len,ex)
  | GrafiteAst.Comment (_,c) -> 
      eval_comment.ecm_go ~disambiguate_command opts status (text,prefix_len,c) 
} and eval_comment = { ecm_go = fun ~disambiguate_command opts status (text,prefix_len,c) -> 
    status, `Old []
}
;;


let eval_ast = eval_ast.ea_go
