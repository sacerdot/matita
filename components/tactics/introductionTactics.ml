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

let fake_constructor_tac ~n (proof, goal) =
  let module C = Cic in
  let module R = CicReduction in
   let (_,metasenv,_subst,_,_, _) = proof in
    let metano,context,ty = CicUtil.lookup_meta goal metasenv in
     match (R.whd context ty) with
        (C.MutInd (uri, typeno, exp_named_subst))
      | (C.Appl ((C.MutInd (uri, typeno, exp_named_subst))::_)) ->
         ProofEngineTypes.apply_tactic (
          PrimitiveTactics.apply_tac 
           ~term: (C.MutConstruct (uri, typeno, n, exp_named_subst)))
           (proof, goal)
      | _ -> raise (ProofEngineTypes.Fail (lazy "Constructor: failed"))
;;

let constructor_tac ~n = ProofEngineTypes.mk_tactic (fake_constructor_tac ~n)

let exists_tac  = ProofEngineTypes.mk_tactic (fake_constructor_tac ~n:1) ;;
let split_tac = ProofEngineTypes.mk_tactic (fake_constructor_tac ~n:1) ;;
let left_tac = ProofEngineTypes.mk_tactic (fake_constructor_tac ~n:1) ;;
let right_tac = ProofEngineTypes.mk_tactic (fake_constructor_tac ~n:2) ;;

