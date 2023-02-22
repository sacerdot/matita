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

include "static_2/syntax/ac.ma".

(* APPLICABILITY CONDITION PREORDER *****************************************)

definition acle: relation ac ≝
           λa1,a2. ∀m. ad a1 m → ∃∃n. ad a2 n & m ≤ n.

interpretation "preorder (applicability domain)"
  'subseteq a1 a2 = (acle a1 a2).

(* Basic properties *********************************************************)

lemma acle_refl: reflexive … acle.
/2 width=3 by ex2_intro/ qed.

lemma acle_omega (a): a ⊆ 𝛚.
/2 width=1 by acle_refl/
qed.

lemma acle_one (a): ∀n. ad a n → 𝟏 ⊆ a.
#a #n #Ha #m #Hm destruct
/2 width=3 by ex2_intro/
qed.

lemma acle_eq_monotonic_le (k1) (k2):
      k1 ≤ k2 → (ac_eq k1) ⊆ (ac_eq k2).
#k1 #k2 #Hk #m #Hm destruct
/2 width=3 by ex2_intro/
qed.

lemma acle_le_monotonic_le (k1) (k2):
      k1 ≤ k2 → (ac_le k1) ⊆ (ac_le k2).
#k1 #k2 #Hk #m #Hm
/3 width=3 by acle_refl, nle_trans/
qed.

lemma acle_eq_le (k): (ac_eq k) ⊆ (ac_le k).
#k #m #Hm destruct
/2 width=1 by nle_refl, acle_refl/
qed.

lemma acle_le_eq (k): (ac_le k) ⊆ (ac_eq k).
#k #m #Hm /2 width=3 by ex2_intro/
qed.
