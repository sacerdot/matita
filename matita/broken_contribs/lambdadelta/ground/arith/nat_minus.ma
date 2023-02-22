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

include "ground/arith/nat_succ_iter.ma".
include "ground/arith/nat_pred_succ.ma".

(* SUBTRACTION FOR NON-NEGATIVE INTEGERS ************************************)

(*** minus *)
definition nminus: nat → nat → nat ≝
           λm,n. (npred^n) m.

interpretation
  "minus (non-negative integers)"
  'minus m n = (nminus m n).

(* Basic constructions ******************************************************)

(*** minus_n_O *)
lemma nminus_zero_dx (m): m = m - 𝟎.
// qed.

(*** minus_SO_dx *)
lemma nminus_unit_dx (m): ↓m = m - 𝟏 .
// qed.

(*** eq_minus_S_pred *)
lemma nminus_succ_dx (m) (n): ↓(m - n) = m - ↑n.
#m #n @(niter_succ … npred)
qed.

(* Advanced constructions ***************************************************)

lemma nminus_pred_sn (m) (n): ↓(m - n) = ↓m - n.
#m #n @(niter_appl … npred)
qed.

(*** minus_O_n *)
lemma nminus_zero_sn (n): 𝟎 = 𝟎 - n.
#n @(nat_ind_succ … n) -n //
qed.

(*** minus_S_S *)
lemma nminus_succ_bi (m) (n): m - n = ↑m - ↑n.
#m #n @(nat_ind_succ … n) -n //
qed.

lemma nminus_succ_dx_pred_sn (m) (n): ↓m - n = m - ↑n.
// qed-.

(*** minus_n_n *)
lemma nminus_refl (m): 𝟎 = m - m.
#m @(nat_ind_succ … m) -m //
qed.

(*** minus_Sn_n *)
lemma nminus_succ_sn_refl (m): ninj (𝟏) = ↑m - m.
#m @(nat_ind_succ … m) -m //
qed.

(*** minus_minus_comm *)
lemma nminus_comm_21 (m) (n1) (n2): m - n1 - n2 = m - n2 - n1.
#m #n1 #n2 @(nat_ind_succ … n2) -n2 //
qed.

(*** minus_minus_comm3 *)
lemma nminus_comm_231 (m) (n1) (n2) (n3):
      m-n1-n2-n3 = m-n2-n3-n1.
// qed.
