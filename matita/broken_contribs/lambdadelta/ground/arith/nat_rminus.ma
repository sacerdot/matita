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

include "ground/arith/pnat_pred.ma".
include "ground/arith/nat_succ_iter.ma".

(* RIGHT SUBTRACTION FOR NON-NEGATIVE INTEGERS ******************************)

definition nrminus: ℕ⁺ → ℕ → ℕ⁺ ≝
           λp,n. (ppred^n) p.

interpretation
  "right minus (non-negative integers)"
  'minus p n = (nrminus p n).

(* Basic constructions ******************************************************)

lemma nrminus_zero_dx (p): p = p - 𝟎.
// qed.

lemma nrminus_unit_dx (p): ⫰p = p - (⁤𝟏).
// qed.

lemma nrminus_succ_dx (p) (n): ⫰(p - n) = p - (⁤↑n).
#p #n @(niter_succ … ppred)
qed.

(* Advanced constructions ***************************************************)

lemma nrminus_pred_sn (p) (n): ⫰(p-n) = ⫰p - n.
#p #n @(niter_appl … ppred)
qed.

lemma nrminus_unit_sn (n): 𝟏 = 𝟏 - n.
#n @(nat_ind_succ … n) -n //
qed.

lemma nrminus_succ_bi (p) (n): p - n = ↑p - (⁤↑n).
#p #n @(nat_ind_succ … n) -n //
qed.
