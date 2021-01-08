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

include "ground/arith/nat_minus_plus.ma".
include "ground/arith/nat_le_plus.ma".
include "ground/arith/nat_le_minus.ma".

(* ORDER FOR NON-NEGATIVE INTEGERS ******************************************)

(* Constructions with nminus and nplus **************************************)

(*** le_plus_minus_m_m *)
lemma nle_plus_minus_sn_refl_sn (n) (m): m ≤ m - n + n.
#n @(nat_ind_succ … n) -n //
#n #IH #m <nminus_succ_dx_pred_sn <nplus_succ_dx
/2 width=1 by nle_inv_pred_sn/
qed.

lemma plus_minus_sn_refl_sn_nle (m) (n): n = n - m + m → m ≤ n.
// qed.

(*** le_plus_to_minus *)
lemma nle_minus_sn (o) (m) (n): m ≤ n + o → m - o ≤ n.
/2 width=1 by nle_minus_sn_bi/ qed.

(*** le_plus_to_minus_r *)
lemma nle_minus_dx (o) (m) (n): m + o ≤ n → m ≤ n - o.
#o #m #n #H >(nminus_plus_sn_refl_sn m o)
/2 width=1 by nle_minus_sn_bi/
qed.

(*** le_inv_plus_l *)
lemma nle_minus_dx_full (o) (m) (n): m + o ≤ n → ∧∧ m ≤ n - o & o ≤ n.
/3 width=3 by nle_minus_dx, nle_trans, conj/ qed-.

(* Inversions with nminus and nplus *****************************************)

(*** plus_minus_m_m *)
lemma nplus_minus_sn_refl_sn (m) (n): m ≤ n → n = n - m + m.
#m #n #H elim H -n //
#n #Hn #IH <(nminus_succ_sn … Hn) -Hn
<nplus_succ_sn //
qed-.

lemma nplus_minus_dx_refl_sn (m) (n): m ≤ n → n = m + (n - m).
#m #n <nplus_comm
/2 width=1 by nplus_minus_sn_refl_sn/
qed-.

(*** le_minus_to_plus *)
lemma nle_inv_minus_sn (o) (m) (n): m - o ≤ n → m ≤ n + o.
/3 width=3 by nle_plus_bi_dx, nle_trans/ qed-.

(*** le_minus_to_plus_r *)
lemma nle_inv_minus_dx (o) (m) (n): o ≤ n → m ≤ n - o → m + o ≤ n.
#o #m #n #Hon #Hm
>(nplus_minus_sn_refl_sn … Hon)
/2 width=1 by nle_plus_bi_dx/
qed-.

(* Destructions with nminus and nplus ***************************************)

(*** plus_minus *)
lemma nminus_plus_comm_23 (o) (m) (n):
      m ≤ n → n - m + o = n + o - m.
#o #m #n #H elim H -n //
#n #Hn #IH <(nminus_succ_sn … Hn)
<nplus_succ_sn <nplus_succ_sn <nminus_succ_sn //
/2 width=3 by nle_trans/
qed-.

(*** plus_minus_associative *)
lemma nplus_minus_assoc (m1) (m2) (n):
      n ≤ m2 → m1 + m2 - n = m1 + (m2 - n).
/2 width=1 by nminus_plus_comm_23/ qed-.

(*** minus_minus_associative *)
theorem nminus_assoc (m1) (m2) (m3):
        m3 ≤ m2 → m2 ≤ m1 → m1 - m2 + m3 = m1 - (m2 - m3).
#m1 #m2 #m3 #Hm32 #Hm21
@nminus_plus_sn >nplus_assoc
<nplus_minus_dx_refl_sn //
/2 width=1 by nplus_minus_sn_refl_sn/
qed-.

(*** minus_minus *)
theorem nminus_assoc_comm (m1) (m2) (m3):
        m3 ≤ m2 → m2 ≤ m1 → m3 + (m1 - m2) = m1 - (m2 - m3).
#m1 #m2 #m3 #Hm32 #Hm21 <nplus_comm
/2 width=1 by nminus_assoc/
qed-.

(*** minus_le_minus_minus_comm *)
theorem minus_assoc_comm_23 (m1) (m2) (m3):
        m3 ≤ m2 → m1 + m3 - m2 = m1 - (m2 - m3).
#m1 #m2 #m3 #Hm
>(nplus_minus_sn_refl_sn … Hm) in ⊢ (??%?); //
qed-.
