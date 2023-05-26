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

include "ground/arith/int_plus_opp.ma".
include "ground/arith/int_le_pred.ma".

(* ORDER FOR INTEGERS *******************************************************)

(* Constructions with zplus *************************************************)

lemma zle_plus_dx_bi (z) (z1) (z2):
      z1 ≤ z2 → z1 + z ≤ z2 + z.
@int_ind_steps //
#z #IH #z1 #z2 #Hz
/3 width=1 by zle_succ_bi, zle_pred_bi/
qed.

lemma zle_minus_zero (z1) (z2):
      z1 ≤ z2 → z1-z2 ≤ 𝟎.
/2 width=1 by zle_plus_dx_bi/
qed.

lemma zle_zero_minus (z1) (z2):
      z1 ≤ z2 → 𝟎 ≤ z2-z1.
#z1 #z2 #Hz
lapply (zle_plus_dx_bi (-z1) … Hz) -Hz //
qed.

(* Inversions with zplus ****************************************************)

lemma zle_inv_minus_zero (z1) (z2):
      z1-z2 ≤ 𝟎 → z1 ≤ z2.
#z1 #z2 #H0
lapply (zle_plus_dx_bi z2 … H0) -H0 //
qed-.

lemma zle_inv_zero_minus (z1) (z2):
      (𝟎) ≤ z2-z1 → z1 ≤ z2.
#z1 #z2 #H0
lapply (zle_plus_dx_bi z1 … H0) -H0 //
qed-.

(* Advanced constructions with zplus ****************************************)

lemma int_split_le_ge (z1) (z2):
      ∨∨ z1 ≤ z2 | z2 ≤ z1.
#z1 #z2 elim (int_split_le_ge_zero (z1-z2))
/3 width=1 by or_introl, or_intror, zle_inv_zero_minus, zle_inv_minus_zero/
qed-.

lemma zle_dec (z1) (z2):
      Decidable … (z1 ≤ z2).
#z1 #z2 elim (int_split_le_ge z1 z2)
[ /2 width=1 by or_introl/
| #Hz elim (eq_int_dec z1 z2)
  [ #H0 destruct /2 width=1 by zle_refl, or_introl/
  | /4 width=1 by zle_antisym, or_intror/
  ]
]
qed-.
