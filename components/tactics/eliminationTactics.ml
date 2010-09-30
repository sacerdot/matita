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

module C    = Cic
module I    = CicInspect
module S    = CicSubstitution
module TC   = CicTypeChecker 
module P    = PrimitiveTactics
module T    = Tacticals
module PESR = ProofEngineStructuralRules
module F    = FreshNamesGenerator
module PET  = ProofEngineTypes
module RT   = ReductionTactics
module E    = CicEnvironment
module R    = CicReduction
module Un   = CicUniv
module PEH  = ProofEngineHelpers

let premise_pattern what = None, [what, C.Implicit (Some `Hole)], None 

let get_inductive_def uri =
   match E.get_obj Un.oblivion_ugraph uri with
      | C.InductiveDefinition (tys, _, lpsno, _), _ -> 
         lpsno, tys
      | _                                           -> assert false

let is_not_recursive uri tyno tys = 
   let map mutinds (_, ty) = 
(* FG: we can do much better here *)      
      let map mutinds (_, t) = I.S.union mutinds (I.get_mutinds_of_uri uri t) in
(**********************************)      
      let premises, _ = PEH.split_with_whd ([], ty) in
      List.fold_left map mutinds (List.tl premises)
   in
   let msg = "recursiveness check non implemented for mutually inductive types" in
   if List.length tys > 1 then raise (PET.Fail (lazy msg)) else
   let _, _, _, constructors = List.nth tys tyno in
   let mutinds = List.fold_left map I.S.empty constructors in
   I.S.is_empty mutinds

let rec check_type sorts metasenv context t = 
   match R.whd ~delta:true context t with
      | C.MutInd (uri, tyno, _) as t -> 
         let lpsno, tys = get_inductive_def uri in
         let _, inductive, arity, _ = List.nth tys tyno in
         let _, psno = PEH.split_with_whd ([], arity) in
         let not_relation = (lpsno = psno) in
         let not_recursive = is_not_recursive uri tyno tys in
         let ty_ty, _ = TC.type_of_aux' metasenv context t Un.oblivion_ugraph in
         let sort = match PEH.split_with_whd (context, ty_ty) with
            | (_, C.Sort sort) ::_ , _ -> CicPp.ppsort sort
	    | (_, C.Meta _) :: _, _    -> CicPp.ppsort (C.Type (Un.fresh ()))
	    | _                        -> assert false
         in
         let right_sort = List.mem sort sorts in
         if not_relation && inductive && not_recursive && right_sort then
	 begin
            HLog.warn (Printf.sprintf "Decomposing %s %u" (UriManager.string_of_uri uri) (succ tyno));
            true 
         end
	 else false 
      | C.Appl (hd :: tl)         -> check_type sorts metasenv context hd
      | _                         -> false

(* unexported tactics *******************************************************)

let rec scan_tac ~old_context_length ~index ~tactic =
   let scan_tac status =
      let (proof, goal) = status in
      let _, metasenv, _subst, _, _, _ = proof in
      let _, context, _ = CicUtil.lookup_meta goal metasenv in
      let context_length = List.length context in
      let rec aux index =
         match PEH.get_name context index with 
	    | _ when index <= 0 -> (proof, [goal])
	    | None              -> aux (pred index)
	    | Some what         -> 
	       let tac = T.then_ ~start:(tactic ~what)
	                         ~continuation:(scan_tac ~old_context_length:context_length ~index ~tactic)
               in
	       try PET.apply_tactic tac status 
	       with PET.Fail _ -> aux (pred index)
      in aux (index + context_length - old_context_length)
   in
   PET.mk_tactic scan_tac

let elim_clear_unfold_tac ~sorts ~mk_fresh_name_callback ~what =
   let elim_clear_unfold_tac status =
      let (proof, goal) = status in
      let _, metasenv, _subst, _, _, _ = proof in
      let _, context, _ = CicUtil.lookup_meta goal metasenv in
      let index, ty = PEH.lookup_type metasenv context what in
      let tac = 
         if check_type sorts metasenv context (S.lift index ty) then 
            T.then_ ~start:(P.elim_intros_tac ~mk_fresh_name_callback (C.Rel index))
	            ~continuation:(PESR.clear [what])
	 else 
	    let msg = "unexported elim_clear: not an decomposable type" in
	    raise (PET.Fail (lazy msg))
      in
      PET.apply_tactic tac status
   in
   PET.mk_tactic elim_clear_unfold_tac

(* elim type ****************************************************************)

let elim_type_tac ?(mk_fresh_name_callback = F.mk_fresh_name ~subst:[]) ?depth
  ?using what
=
  let elim =
    P.elim_intros_simpl_tac ?using ?depth ~mk_fresh_name_callback
  in
  let elim_type_tac status =
    let tac =
      T.thens ~start: (P.cut_tac what) ~continuations:[elim (C.Rel 1); T.id_tac]
    in
    PET.apply_tactic tac status
  in
  PET.mk_tactic elim_type_tac

(* decompose ****************************************************************)

(* robaglia --------------------------------------------------------------- *)

  (** perform debugging output? *)
let debug = false
let debug_print = fun _ -> ()

  (** debugging print *)
let warn s = debug_print (lazy ("DECOMPOSE: " ^ (Lazy.force s)))

(* roba seria ------------------------------------------------------------- *)

let decompose_tac ?(sorts=[CicPp.ppsort C.Prop; CicPp.ppsort (C.CProp (CicUniv.fresh ()))]) 
                  ?(mk_fresh_name_callback = F.mk_fresh_name ~subst:[]) () =
   let decompose_tac status =
      let (proof, goal) = status in
      let _, metasenv, _subst, _,_, _ = proof in
      let _, context, _ = CicUtil.lookup_meta goal metasenv in
      let tactic = elim_clear_unfold_tac ~sorts ~mk_fresh_name_callback in
      let old_context_length = List.length context in      
      let tac = scan_tac ~old_context_length ~index:old_context_length ~tactic
      in
      PET.apply_tactic tac status
   in
   PET.mk_tactic decompose_tac
