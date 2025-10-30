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

include "ground/arith/nat_max.ma".
include "ground/arith/nat_le.ma".

(* ORDER FOR NON-NEGATIVE INTEGERS ******************************************)

(* Basic constructions with nmax ********************************************)

(*** to_max *)
lemma nle_max_sx (n):
      ∀m1. m1 ≤ n → ∀m2. m2 ≤ n → (m1 ∨ m2) ≤ n.
#n #m1 #H @(nle_ind_alt … H) -n -m1 //
#n #m1 #Hnm1 #IH #m2 @(nat_ind_succ … m2) -m2
[ #_ -IH /3 width=1 by nle_succ_bi/
| #m2 #_ #H -Hnm1 /4 width=1 by nle_inv_succ_bi, nle_succ_bi/
]
qed.

lemma nle_max_dx_refl_sx (m) (n): m ≤ (m ∨ n).
#m #n @(nat_ind_2_succ … m n) -m -n //
#m #n #IH <nmax_succ_bi /2 width=1 by nle_succ_bi/
qed.

lemma nle_max_dx_refl_dx (m) (n): n ≤ (m ∨ n).
// qed.

(* Basic destructions with nmax *********************************************)

(*** le_maxl *)
lemma nle_des_max_sx_sx (m1) (m2) (n): (m1 ∨ m2) ≤ n → m1 ≤ n.
/2 width=3 by nle_trans/ qed-.

(*** le_maxr *)
lemma nle_des_max_sx_dx (m1) (m2) (n): (m1 ∨ m2) ≤ n → m2 ≤ n.
/2 width=3 by nle_trans/ qed-.

(* Advanced constructions with nmax *****************************************)

(*** max_S1_le_S *)
lemma nle_max_sx_succ_sx (m1) (m2) (n): (m1 ∨ m2) ≤ n → ((⁤↑m1) ∨ m2) ≤ (⁤↑n).
/4 width=2 by nle_des_max_sx_sx, nle_des_max_sx_dx, nle_max_sx, nle_succ_bi, nle_succ_dx/ qed.

(*** max_S2_le_S *)
lemma nle_max_sx_succ_dx (m1) (m2) (n): (m1 ∨ m2) ≤ n → (m1 ∨ (⁤↑m2)) ≤ (⁤↑n).
/4 width=2 by nle_des_max_sx_sx, nle_des_max_sx_dx, nle_max_sx, nle_succ_bi, nle_succ_dx/ qed.
