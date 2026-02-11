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

include "ground/lib/functions.ma".
include "ground/subsets/subset_le.ma".
include "ground/subsets/subset_or.ma".

(* UNION FOR SUBSETS ********************************************************)

(* Constructions with subset_le *********************************************)

lemma subset_le_or_sx (A) (u1) (u2) (v:𝒫❨A❩): (**)
      u1 ⊆ v → u2 ⊆ v → u1 ∪ u2 ⊆ v.
#A #u1 #u2 #v #Hu1 #Hu2 #p * #Hp
/3 width=1 by/
qed.

lemma subset_le_or_dx_refl_sx (A) (u1) (u2:𝒫❨A❩): (**)
      u1 ⊆ u1 ∪ u2.
/2 width=1 by subset_or_in_sx/
qed.

lemma subset_le_or_dx_refl_dx (A) (u1:𝒫❨A❩) (u2): (**)
      u2 ⊆ u1 ∪ u2.
/2 width=1 by subset_or_in_dx/
qed.

lemma subset_le_or_sx_refl_sx (A) (u1) (u2:𝒫❨A❩): (**)
      u1 ⊆ u2 → u2 ∪ u1 ⊆ u2.
/2 width=5 by subset_le_or_sx/
qed.

lemma subset_le_or_sx_refl_dx (A) (u1) (u2:𝒫❨A❩): (**)
      u1 ⊆ u2 → u1 ∪ u2 ⊆ u2.
/2 width=5 by subset_le_or_sx/
qed.

lemma subset_le_or_sx_refl_bi (A) (u:𝒫❨A❩): (**)
      u ∪ u ⊆ u.
/2 width=3 by subset_le_or_sx_refl_sx/
qed.

lemma subset_dx_le_or (A) (u:𝒫❨A❩) (v1) (v2): (**)
      u ⊆ v2 → u ⊆ v1 ∪ v2.
#U #u #v1 #v2 #H0
@(subset_le_trans … H0) -H0 //
qed.

(* Inversions with subset_le ************************************************)

lemma subset_le_or_inv_sx_sx (A) (u1) (u2) (v:𝒫❨A❩): (**)
      u1 ∪ u2 ⊆ v → u1 ⊆ v.
/3 width=1 by subset_or_in_sx/
qed-.

lemma subset_le_or_inv_sx_dx (A) (u1) (u2) (v:𝒫❨A❩): (**)
      u1 ∪ u2 ⊆ v → u2 ⊆ v.
/3 width=1 by subset_or_in_dx/
qed-.

(* Main constructions with subset_le ****************************************)

theorem subset_or_le_repl (A):
        compatible_3 … (subset_le …) (subset_le …) (subset_le …) (subset_or A).
#A #u1 #v1 #H1 #u2 #v2 #H2
/4 width=5 by subset_le_or_sx, subset_or_in_dx, subset_or_in_sx/
qed.
