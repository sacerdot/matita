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

include "ground/arith/nat_le_pred.ma".
include "ground/arith/nat_lt_le.ma".

(* STRICT ORDER FOR NON-NEGATIVE INTEGERS ***********************************)

(* Destructions with npred **************************************************)

(*** S_pred lt_succ_pred lt_inv_O1 *)
lemma nlt_des_gen (m) (n): m < n → n ϵ 𝐏.
#m #n @(nat_ind_succ … n) -n //
#H elim (nlt_inv_zero_dx … H)
qed-.

(* Inversions with npred ****************************************************)

(*** lt_inv_gen *)
lemma nlt_inv_gen (m) (n): m < n → ∧∧ m ≤ ⫰n & n ϵ 𝐏.
/3 width=1 by nlt_inv_le, nle_inv_succ_sx/
qed-.

(*** lt_inv_S1 *)
lemma nlt_inv_succ_sx (m) (n): (⁤↑m) < n → ∧∧ m < ⫰n & n ϵ 𝐏.
#m #n #H0
lapply (nlt_inv_le … H0) -H0 #H0
elim (nle_inv_succ_sx … H0) -H0 #H0 #Hn
/3 width=1 by nlt_le, conj/
qed-.

lemma nlt_inv_pred_dx (m) (n): m < ⫰n → (⁤↑m) < n.
#m #n #H >(nlt_des_gen (𝟎) n)
[ /2 width=1 by nlt_succ_bi/
| /3 width=3 by nle_nlt_trans, nlt_nle_trans/
]
qed-.

lemma nlt_inv_pred_bi (m) (n):
      (⫰m) < ⫰n → m < n.
/3 width=3 by nlt_inv_pred_dx, nle_nlt_trans/
qed-.

(* Constructions with npred *************************************************)

lemma nlt_zero_sx (n): n ϵ 𝐏 → 𝟎 < n.
//
qed.

(*** monotonic_lt_pred *)
lemma nlt_pred_bi (m) (n): 𝟎 < m → m < n → ⫰m < ⫰n.
#m #n #Hm #Hmn
@nlt_le
@nle_inv_succ_bi
<(nlt_des_gen … Hm) -Hm
<(nlt_des_gen … Hmn)
/2 width=1 by nlt_inv_le/
qed.
