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
include "ground/arith/nat_le_pred.ma".

(* ORDER FOR NON-NEGATIVE INTEGERS ******************************************)

(* Constructions with nminus ************************************************)

(*** minus_le *)
lemma nle_minus_sn_refl_sn (m) (n): m - n ≤ m.
#m #n @(nat_ind_succ … n) -n //
#n #IH /2 width=3 by nle_trans/
qed.

lemma nle_minus_succ_sn (m) (n): (⁤↑n) - m ≤ (⁤↑(n - m)).
#m #n
@nle_inv_pred_sn >nminus_pred_sn //
qed.

(*** inv_eq_minus_O *)
lemma nle_eq_zero_minus (m) (n): 𝟎 = m - n → m ≤ n.
#m #n @(nat_ind_2_succ … m n) //
#m #n #IH <nminus_succ_bi
/3 width=1 by nle_succ_bi/
qed.

(*** monotonic_le_minus_l *)
lemma nle_minus_bi_dx (m) (n) (o): m ≤ n → m-o ≤ n-o.
#m #n #o @(nat_ind_succ … o) -o //
#o #IH #Hmn /3 width=1 by nle_pred_bi/
qed.

(*** monotonic_le_minus_r *)
lemma nle_minus_bi_sn (m) (n) (o): m ≤ n → o-n ≤ o-m.
#m #n #o #H elim H -n //
#n #_ #IH /2 width=3 by nle_trans/
qed.

(*** minus_le_trans_sn *)
lemma nle_minus_sn (o) (m) (n): m ≤ n → m - o ≤ n.
/2 width=3 by nle_trans/ qed.

(* Inversions with nminus ***************************************************)

(*** eq_minus_O *)
lemma nle_inv_eq_zero_minus (m) (n): m ≤ n → 𝟎 = m - n.
#m #n #H elim H -n //
qed-.

(* Destructions with nminus *************************************************)

(*** minus_Sn_m *)
lemma nminus_succ_sn (m) (n): m ≤ n → (⁤↑(n-m)) = (⁤↑n) - m.
#m #n #H @(nle_ind_alt … H) -m -n //
qed-.

(*** minus_minus_m_m *)
lemma nminus_minus_dx_refl_sn (m) (n): m ≤ n → m = n - (n - m).
#m #n #H elim H -n //
#n #Hmn #IH <(nminus_succ_sn … Hmn) -Hmn
<nminus_succ_bi //
qed-.
