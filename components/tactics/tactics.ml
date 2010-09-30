(* Copyright (C) 2004, HELM Team.
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

let absurd = NegationTactics.absurd_tac
let apply = PrimitiveTactics.apply_tac
let applyP = PrimitiveTactics.applyP_tac
let applyS = Auto.applyS_tac
let assumption = VariousTactics.assumption_tac
let auto = Auto.auto_tac
let cases_intros = PrimitiveTactics.cases_intros_tac
let change = ReductionTactics.change_tac
let clear = ProofEngineStructuralRules.clear
let clearbody = ProofEngineStructuralRules.clearbody
let constructor = IntroductionTactics.constructor_tac
let contradiction = NegationTactics.contradiction_tac
let cut = PrimitiveTactics.cut_tac
let decompose = EliminationTactics.decompose_tac
let demodulate = Auto.demodulate_tac
let destruct = DestructTactic.destruct_tac
let elim_intros = PrimitiveTactics.elim_intros_tac
let elim_intros_simpl = PrimitiveTactics.elim_intros_simpl_tac
let elim_type = EliminationTactics.elim_type_tac
let exact = PrimitiveTactics.exact_tac
let exists = IntroductionTactics.exists_tac
let fail = Tacticals.fail_tac
let fold = ReductionTactics.fold_tac
let fourier = FourierR.fourier_tac
let fwd_simpl = FwdSimplTactic.fwd_simpl_tac
let generalize = PrimitiveTactics.generalize_tac
let id = Tacticals.id_tac
let intros = PrimitiveTactics.intros_tac
let inversion = Inversion.inversion_tac
let lapply = FwdSimplTactic.lapply_tac
let left = IntroductionTactics.left_tac
let letin = PrimitiveTactics.letin_tac
let normalize = ReductionTactics.normalize_tac
let reflexivity = Setoids.setoid_reflexivity_tac
let replace = EqualityTactics.replace_tac
let rewrite = EqualityTactics.rewrite_tac
let rewrite_simpl = EqualityTactics.rewrite_simpl_tac
let right = IntroductionTactics.right_tac
let ring = Ring.ring_tac
let simpl = ReductionTactics.simpl_tac
let split = IntroductionTactics.split_tac
let symmetry = EqualityTactics.symmetry_tac
let transitivity = EqualityTactics.transitivity_tac
let unfold = ReductionTactics.unfold_tac
let whd = ReductionTactics.whd_tac
let compose = Compose.compose_tac

(* keep linked *)
let _ = CloseCoercionGraph.close_coercion_graph;;
