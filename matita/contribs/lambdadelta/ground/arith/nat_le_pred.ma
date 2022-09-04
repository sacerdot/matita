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

include "ground/arith/nat_pred_succ.ma".
include "ground/arith/nat_le.ma".

(* ORDER FOR NON-NEGATIVE INTEGERS ******************************************)

(* Inversions with npred ****************************************************)

lemma nle_inv_pred_sn (m) (n): ↓m ≤ n → m ≤ ↑n.
#m #n @(nat_ind_succ … m) -m
/2 width=1 by nle_succ_bi/
qed-.

(*** le_inv_S1 *)
lemma nle_inv_succ_sn (m) (n):
      ↑m ≤ n → ∧∧ m ≤ ↓n & n = ↑↓n.
#m #n * -n
[ /2 width=3 by nle_refl, conj/
| #n #Hn /3 width=1 by nle_des_succ_sn, conj/
]
qed-.

lemma nle_inv_succ_dx (m) (n):
      m ≤ ↑n → ∨∨ 𝟎 = m | ∧∧ ↓m ≤ n & m = ↑↓m.
#m #n @(nat_ind_succ … m) -m
[ /2 width=1 by or_introl/
| #m #_ #H0
  /4 width=1 by nle_inv_succ_bi, or_intror, conj/
]
qed-.

(* Constructions with npred *************************************************)

lemma nle_succ_pred_dx_refl (m): m ≤ ↑↓m.
#m @nle_inv_pred_sn // qed.

(*** le_pred_n *)
lemma nle_pred_sn_refl (m): ↓m ≤ m.
#m @(nat_ind_succ … m) -m //
qed.

(*** monotonic_pred *)
lemma nle_pred_bi (m) (n): m ≤ n → ↓m ≤ ↓n.
#m #n #H elim H -n //
/2 width=3 by nle_trans/
qed.

lemma nle_pred_sn (m) (n): m ≤ ↑n → ↓m ≤ n.
#m #n @(nat_ind_succ … m) -m //
/2 width=1 by nle_pred_bi/
qed.
