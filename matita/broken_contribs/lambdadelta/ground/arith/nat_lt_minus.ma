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

include "ground/generated/pull_2.ma".
include "ground/arith/nat_le_minus.ma".
include "ground/arith/nat_lt_pred.ma".

(* STRICT ORDER FOR NON-NEGATIVE INTEGERS ***********************************)

(* Constructions with nminus ************************************************)

(*** monotonic_lt_minus_l *)
lemma nlt_minus_bi_dx (o) (m) (n): o ≤ m → m < n → m - o < n - o.
#o #m #n #Hom #Hmn
lapply (nle_minus_bi_dx … o Hmn) -Hmn
<(nminus_succ_sx … Hom) //
qed.

(*** monotonic_lt_minus_r *)
lemma nlt_minus_bi_sx (o) (m) (n):
      m < o -> m < n → o-n < o-m.
#o #m #n #Ho #H
lapply (nle_minus_bi_sx … o H) -H #H
@(nle_nlt_trans … H) -n
@nlt_i >(nminus_succ_sx … Ho) //
qed.

(* Inversions with nminus ***************************************************)

lemma nlt_inv_minus_bi_dx (o) (m) (n):
      m - o < n - o → m < n.
#o @(nat_ind_succ … o) -o
/3 width=1 by nlt_inv_pred_bi/
qed-.

(* Destructions with nminus *************************************************)

(*** minus_pred_pred *)
lemma nminus_pred_bi (m) (n): 𝟎 < m → 𝟎 < n → n - m = ⫰n - ⫰m.
#m #n #Hm #Hn
>(nlt_des_gen … Hm) in ⊢ (??%?); -Hm
>(nlt_des_gen … Hn) in ⊢ (??%?); -Hn
//
qed-.

lemma nlt_des_minus_dx (o) (m) (n): m < n - o → o < n.
#o @(nat_ind_succ … o) -o
[ #m #n <nminus_zero_dx
  /2 width=3 by nle_nlt_trans/
| #o #IH #m #n <nminus_succ_dx_pred_sx #H
  /3 width=2 by nlt_inv_pred_dx/
]
qed-.

(* Advanced eliminators for nle with nlt and nminus *************************)

(*** nat_elim_le_sx *)
lemma nle_ind_sx (Q:relation …):
      (∀m1,m2. (∀m. m < m2-m1 → Q (m2-m) m2) → m1 ≤ m2 → Q m1 m2) →
      ∀n1,n2. n1 ≤ n2 → Q n1 n2.
#Q #IH #n1 #n2 #Hn
>(nminus_minus_dx_refl_sx … Hn) -Hn
lapply (nle_minus_sx_refl_sx n2 n1)
let d ≝ (n2-n1)
@(nat_ind_lt … d) -d -n1 #d
@pull_2 #Hd
>(nminus_minus_dx_refl_sx … Hd) in ⊢ (%→?); -Hd
let n1 ≝ (n2-d) #IHd
@IH -IH [| // ] #m #Hn
/4 width=3 by nlt_des_le, nlt_nle_trans/
qed-.
