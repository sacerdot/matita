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

include "ground/subsets/subset_listed_or_le.ma".
include "ground/subsets/subset_listed_nimply_le.ma".

(* DIFFERENCE FOR SUBSETS ***************************************************)

(* Constructions with subset_or and subset_le *******************************)

lemma subset_le_nimp_or_sx (A) (u1) (u2) (v:𝒫❨A❩): (**)
      (u1 ∪ u2) ⧵ v ⊆ (u1 ⧵ v) ∪ (u2 ⧵ v).
#A #u1 #u2 #v #a * * #Hu #Hnv
/3 width=1 by subset_in_nimp, subset_or_in_dx, subset_or_in_sx/
qed.

lemma subset_le_nimp_or_sx_refl_sx (A) (u1) (u2:𝒫❨A❩): (**)
      u1 ∪ u2 ⧵ u1 ⊆ u2.
#A #u1 #u2
@(subset_le_trans … (subset_le_nimp_or_sx …))
@(subset_le_trans ??? (subset_or_le_repl ?? (Ⓕ) ?? u2 …))
[ /2 width=5 by subset_le_nimp_sx_refl_sx/
| /2 width=2 by subset_le_nimp_refl_empty/
| /2 width=1 by subset_le_or_sx_empty_refl/
]
qed.

lemma subset_le_or_dx_nimp_sx_refl_bi (A) (u1) (u2): (**)
      (∀a. Decidable (a ϵ u2)) →
      u1 ⊆ (u1 ⧵❪A❫ u2) ∪ u2.
#A #u1 #u2 #Hu2 #a #Ha
elim (Hu2 a) -Hu2 #Hu2
[ /2 width=1 by subset_or_in_dx/
| /4 width=1 by subset_in_nimp, subset_or_in_sx/
]
qed.

lemma subset_le_or_dx_nimp_dx_refl_bi (A) (u1) (u2): (**)
      (∀a. Decidable (a ϵ u2)) →
      u1 ⊆ u2 ∪ (u1 ⧵❪A❫ u2).
#A #u1 #u2 #Hu2 #a #Ha
elim (Hu2 a) -Hu2 #Hu2
[ /2 width=1 by subset_or_in_sx/
| /4 width=1 by subset_in_nimp, subset_or_in_dx/
]
qed.
