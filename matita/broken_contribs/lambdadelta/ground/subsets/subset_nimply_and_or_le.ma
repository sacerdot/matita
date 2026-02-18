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

include "ground/subsets/subset_le.ma".
include "ground/subsets/subset_or.ma".
include "ground/subsets/subset_and.ma".
include "ground/subsets/subset_nimply.ma".

(* DIFFERENCE FOR SUBSETS ***************************************************)

(* Constructions with subset_and and subset_or and subset_le ****************)

lemma subset_le_nimp_and_dx (A) (u:𝒫❨A❩) (v1) (v2): (**)
      (∀a. ∨∨ Decidable (a ϵ v1) | Decidable (a ϵ v2)) →
      u ⧵ (v1 ∩ v2) ⊆ (u ⧵ v1) ∪ (u ⧵ v2).
#A #u #v1 #v2 #Hv #a * #Ha #H0
elim (subset_nin_inv_and ???? (Hv a) H0) -H0 #H0a
/4 width=1 by subset_in_nimp, subset_or_in_dx, subset_or_in_sx/
qed.

lemma subset_ge_nimp_and_dx (A) (u:𝒫❨A❩) (v1) (v2): (**)
      (u ⧵ v1) ∪ (u ⧵ v2) ⊆ u ⧵ (v1 ∩ v2).
#A #u #v1 #v2 #a * * #Ha #Hna
/3 width=6 by subset_in_nimp, subset_nin_and_dx, subset_nin_and_sx/ 
qed.

lemma subset_le_or_dx_and_nimp_refl_sx_bi (A) (u) (v):
      (∀a. Decidable (a ϵ❪A❫ v)) →
      u ⊆ (u ∩ v) ∪ (u ⧵ v).
#A #u #v #Hu #a #Ha
elim (Hu a) #Hna
[ /3 width=1 by subset_or_in_sx, subset_and_in/
| /4 width=1 by subset_in_nimp, subset_or_in_dx/
]
qed.

lemma subset_le_or_sx_and_nimp_refl_sx_bi (A) (u) (v):
      (∀a. Decidable (a ϵ❪A❫ v)) →
      (u ∩ v) ∪ (u ⧵ v) ⊆ u.
#A #u #v #Hu #a * * //
qed.

lemma subset_le_nimp_or_dx (A) (u:𝒫❨A❩) (v1) (v2): (**)
      u ⧵ (v1 ∪ v2) ⊆ (u ⧵ v1) ∩ (u ⧵ v2).
#A #u #v1 #v2 #a * #Ha #H0
elim (subset_nin_inv_or ???? H0) -H0 #H1a #H2a
/4 width=3 by subset_and_in/
qed.
