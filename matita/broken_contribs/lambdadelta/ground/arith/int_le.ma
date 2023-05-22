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

include "ground/generated/insert_eq_1.ma".
include "ground/arith/int_succ.ma".

(* ORDER FOR INTEGERS *******************************************************)

inductive zle (z1:ℤ): predicate (ℤ) ≝
| zle_refl        : zle z1 z1
| zle_succ_dx (z2): zle z1 z2 → zle z1 (↑z2)
.

interpretation
  "less or equal (integers)"
  'leq z1 z2 = (zle z1 z2).

(* Basic constructions ******************************************************)

lemma zle_self_succ (z):
      z ≤ ↑z.
/2 width=1 by zle_refl, zle_succ_dx/
qed.

lemma zle_succ_bi (z1) (z2):
      z1 ≤ z2 → ↑z1 ≤ ↑z2.
#z1 #z2 #H elim H -z2
/2 width=1 by zle_refl, zle_succ_dx/
qed.

lemma zle_zero_pos (p):
      (𝟎) ≤ ⁤p.
#p elim p -p
/2 width=1 by zle_succ_dx/
qed.

(* Basic destructions *******************************************************)

lemma zle_des_succ_sn (z1) (z2):
      ↑z1 ≤ z2 → z1 ≤ z2.
#z1 #z2 #H0 elim H0 -z2
/2 width=1 by zle_succ_dx/
qed-.

lemma zle_des_pos_sn (p) (z):
     (⁤p) ≤ z →
     ∃q. (⁤q) = z.
#p #z #H0 elim H0 -z
[ /2 width=2 by ex_intro/
| #z #_ * #q #H0 destruct
  /2 width=2 by ex_intro/
]
qed-.

(* Advanced inversions *****************************************************)

lemma zle_inv_pos_zero (p):
      (⁤p) ≤ 𝟎 → ⊥.
#p #H0
elim (zle_des_pos_sn … H0) -H0 #q #H0 destruct
qed-.

(* Main constructions ******************************************************)

(*** transitive_le *)
theorem zle_trans: Transitive … zle.
#z1 #z2 #H0 elim H0 -z2
/3 width=1 by zle_des_succ_sn/
qed-.
