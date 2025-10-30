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

include "ground/arith/nat_minus.ma".
include "ground/arith/ynat_pred.ma".

(* LEFT SUBTRACTION FOR NON-NEGATIVE INTEGERS WITH INFINITY *****************)

(*** yminus_sx *)
definition ylminus (x) (n): ynat ≝
           (ypred^n) x.

interpretation
  "left minus (non-negative integers with infinity)"
  'minus x n = (ylminus x n).

(* Basic constructions ******************************************************)

(*** yminus_O2 *)
lemma ylminus_zero_dx (x:ynat): x = x - 𝟎 .
// qed.

(*** yminus_pred1 *)
lemma yminus_pred_sx (x) (n): ⫰(x-n) = ⫰x - n.
#x #n @(niter_appl … ypred)
qed.

(*** yminus_succ2 yminus_S2 *)
lemma ylminus_succ_dx (x:ynat) (n): ⫰(x-n) = x - (⁤↑n).
#x #n @(niter_succ … ypred)
qed.

(*** yminus_SO2 *)
lemma ylminus_unit_dx (x): ⫰x = x - (⁤𝟏).
// qed.

(*** yminus_Y_inj *)
lemma ylminus_inf_sx (n): ∞ = ∞ - n.
#n @(nat_ind_succ … n) -n //
qed.

(* Constructions with nminus ************************************************)

(*** yminus_inj *)
lemma ylminus_inj_sx (m) (n): yinj_nat (m - n) = yinj_nat m - n.
#m #n
@(niter_compose ???? yinj_nat)
@ypred_inj
qed.

(* Advanced constructions ***************************************************)

(*** yminus_O1 *)
lemma ylminus_zero_sx (n): 𝟎 = 𝟎 - n.
// qed.

(*** yminus_refl *)
lemma ylminus_refl (n): 𝟎 = yinj_nat n - n.
// qed.

(*** yminus_minus_comm *)
lemma ylminus_minus_comm (x) (n) (o):
      x - n - o = x - o - n.
#x @(ynat_split_nat_inf … x) -x //
qed.
