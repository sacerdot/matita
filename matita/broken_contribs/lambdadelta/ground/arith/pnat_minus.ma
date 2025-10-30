(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "ground/arith/pnat_iter.ma".
include "ground/arith/pnat_pred.ma".

(* SUBTRACTION FOR NON-NEGATIVE INTEGERS ************************************)

definition pminus: ℕ⁺ → ℕ⁺ → ℕ⁺ ≝
           λp,q. (ppred^q) p.

interpretation
  "minus (positive integers)"
  'minus p q = (pminus p q).

(* Basic constructions ******************************************************)

lemma pminus_unit_dx (p): ⫰p = p - 𝟏.
// qed.

lemma pminus_succ_dx (p) (q): ⫰(p - q) = p - ↑q.
#p #q @(piter_succ … ppred)
qed.

(* Advanced constructions ***************************************************)

lemma pminus_pred_sx (p) (q): ⫰(p - q) = ⫰p - q.
#p #q @(piter_appl … ppred)
qed.

lemma pminus_unit_sx (q): 𝟏 = 𝟏 - q.
#q elim q -q //
qed.

lemma pminus_succ_bi (p) (q): p - q = ↑p - ↑q.
#p #q elim q -q //
qed.

lemma pminus_succ_dx_pred_sx (p) (q): ⫰p - q = p - ↑q.
// qed-.

lemma pminus_refl (p): 𝟏 = p - p.
#p elim p -p //
qed.

lemma pminus_succ_sx_refl (p): 𝟏 = ↑p - p.
#p elim p -p //
qed.

lemma pminus_comm_21 (p) (q1) (q2): p - q1 - q2 = p - q2 - q1.
#p #q1 #q2 elim q2 -q2 //
qed.

lemma pminus_comm_231 (p) (q1) (q2) (q3):
      p-q1-q2-q3 = p-q2-q3-q1.
// qed.
