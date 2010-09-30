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

module PEH = ProofEngineHelpers 
module U  = CicUniv
module TC = CicTypeChecker 
module PET = ProofEngineTypes 
module S = CicSubstitution
module PT = PrimitiveTactics
module T = Tacticals
module FNG = FreshNamesGenerator
module MI = CicMkImplicit
module PESR = ProofEngineStructuralRules
module HEL = HExtlib

let fail_msg0 = "unexported clearbody: invalid argument"
let fail_msg2 = "fwd: no applicable simplification"

let error msg = raise (PET.Fail (lazy msg))

(* unexported tactics *******************************************************)

let id_tac = 
   let id_tac (proof,goal) = 
      try
         let _, metasenv, _subst, _, _, _ = proof in
         let _, _, _ = CicUtil.lookup_meta goal metasenv in
         (proof,[goal])
      with CicUtil.Meta_not_found _ -> (proof, [])
   in 
   PET.mk_tactic id_tac

let clearbody ~index =
   let rec find_name index = function
      | Some (Cic.Name name, _) :: _ when index = 1 -> name
      | _ :: tail when index > 1 -> find_name (pred index) tail
      | _ -> error fail_msg0
   in
   let clearbody status =
      let (proof, goal) = status in
      let _, metasenv, _subst, _, _, _ = proof in
      let _, context, _ = CicUtil.lookup_meta goal metasenv in
      PET.apply_tactic (PESR.clearbody ~hyp:(find_name index context)) status
   in
   PET.mk_tactic clearbody

(* lapply *******************************************************************)

let strip_prods metasenv context ?how_many to_what term =
   let irl = MI.identity_relocation_list_for_metavariable context in
   let mk_meta metasenv its_type =  
      let index = MI.new_meta metasenv [] in
      let metasenv = [index, context, its_type] @ metasenv in
      metasenv, Cic.Meta (index, irl), index
   in
   let update_counters = function
      | None, []                 -> None, false, id_tac, []
      | None, to_what :: tail    -> None, true, PT.apply_tac ~term:to_what, tail
      | Some hm, []              -> Some (pred hm), false, id_tac, []
      | Some hm, to_what :: tail -> Some (pred hm), true, PT.apply_tac ~term:to_what, tail
   in 
   let rec aux metasenv metas conts tw = function
      | Some hm, _ when hm <= 0               -> metasenv, metas, conts 
      | xhm, Cic.Prod (Cic.Name _, t1, t2)    ->
         let metasenv, meta, index = mk_meta metasenv t1 in    
	 aux metasenv (meta :: metas) (conts @ [id_tac, index]) tw (xhm, (S.subst meta t2))      
      | xhm, Cic.Prod (Cic.Anonymous, t1, t2) ->
         let xhm, pos, tac, tw = update_counters (xhm, tw) in 
         let metasenv, meta, index = mk_meta metasenv t1 in    
	 let conts = if pos then (tac, index) :: conts else conts @ [tac, index] in 
	 aux metasenv (meta :: metas) conts tw (xhm, (S.subst meta t2))
      | _, t                                  -> metasenv, metas, conts 
   in
   aux metasenv [] [] to_what (how_many, term)

let get_clearables context terms =
   let aux = function
      | Cic.Rel i 
      | Cic.Appl (Cic.Rel i :: _) -> PEH.get_name context i
      | _                         -> None
   in
   HEL.list_rev_map_filter aux terms 

let lapply_tac_aux ?(mk_fresh_name_callback = FreshNamesGenerator.mk_fresh_name ~subst:[]) 
               (* ?(substs = []) *) ?how_many ?(to_what = []) what =
   let letin_tac term = PT.letin_tac ~mk_fresh_name_callback term in   
   let lapply_tac (proof, goal) =
      let xuri, metasenv, _subst, u, t, attrs = proof in
      let _, context, _ = CicUtil.lookup_meta goal metasenv in
      let lemma, _ = TC.type_of_aux' metasenv context what U.oblivion_ugraph in
      let lemma = FNG.clean_dummy_dependent_types lemma in
      let metasenv, metas, conts = strip_prods metasenv context ?how_many to_what lemma in
      let conclusion =  
         match metas with [] -> what | _ -> Cic.Appl (what :: List.rev metas)
      in
      let tac =
	 T.then_ ~start:(letin_tac conclusion) 
                 ~continuation:(clearbody ~index:1)	 
      in
      let proof = (xuri, metasenv, _subst, u, t, attrs) in
      let aux (proof, goals) (tac, goal) = 
         let proof, new_goals = PET.apply_tactic tac (proof, goal) in
	 proof, goals @ new_goals
      in
      List.fold_left aux (proof, []) ((tac, goal) :: conts)
   in
   PET.mk_tactic lapply_tac

let lapply_tac ?(mk_fresh_name_callback = FreshNamesGenerator.mk_fresh_name ~subst:[]) 
               (* ?(substs = []) *) ?(linear = false) ?how_many ?(to_what = []) what =
   let lapply_tac status =
      let proof, goal = status in
      let _, metasenv, _subst, _, _, _ = proof in
      let _, context, _ = CicUtil.lookup_meta goal metasenv in
      let lapply = lapply_tac_aux ~mk_fresh_name_callback ?how_many ~to_what what in
      let tac =  
         if linear then 
            let hyps = get_clearables context (what :: to_what) in
	    T.then_ ~start:lapply
	            ~continuation:(PESR.clear ~hyps) (* T.try_tactic ~tactic: *)
	 else 
	    lapply    
	 in
	 PET.apply_tactic tac status
   in
   PET.mk_tactic lapply_tac

(* fwd **********************************************************************)

let fwd_simpl_tac
     ?(mk_fresh_name_callback = FNG.mk_fresh_name ~subst:[])
     ~dbd hyp =
   let lapply_tac to_what lemma = 
      lapply_tac ~mk_fresh_name_callback ~how_many:1 ~to_what:[to_what] lemma
   in
   let fwd_simpl_tac status =
      let (proof, goal) = status in
      let _, metasenv, _subst, _, _, _ = proof in
      let _, context, ty = CicUtil.lookup_meta goal metasenv in
      let index, major = PEH.lookup_type metasenv context hyp in 
      match FwdQueries.fwd_simpl ~dbd major with
         | []       -> error fail_msg2
         | uri :: _ -> 
	    Printf.eprintf "fwd: %s\n" (UriManager.string_of_uri uri); flush stderr;
	    let start = lapply_tac (Cic.Rel index) (Cic.Const (uri, [])) in  
            let tac = T.then_ ~start ~continuation:(PESR.clear ~hyps:[hyp]) in
            PET.apply_tactic tac status
   in
   PET.mk_tactic fwd_simpl_tac
