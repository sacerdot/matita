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
include "ground/subsets/subset_or_3.ma".

(* TERNARY UNION FOR SUBSETS ************************************************)

(* Base constructions with subset_le ****************************************)

lemma subset_le_or_3_dx_refl_sx (A) (u1) (u2) (u3):
      u1 ⊆ ∪∪❪A❫ u1 | u2 | u3.
/2 width=1 by subset_or_3_in_sx/
qed.

lemma subset_le_or_3_dx_refl_rc (A) (u1) (u2) (u3):
      u2 ⊆ ∪∪❪A❫ u1 | u2 | u3.
/2 width=1 by subset_or_3_in_rc/
qed.

lemma subset_le_or_3_dx_refl_dx (A) (u1) (u2) (u3):
      u3 ⊆ ∪∪❪A❫ u1 | u2 | u3.
/2 width=1 by subset_or_3_in_dx/
qed.

lemma subset_le_or_3_sx (A) (u1) (u2) (u3) (v):
      u1 ⊆ v → u2 ⊆ v → u3 ⊆ v → ∪∪❪A❫ u1 | u2 | u3 ⊆ v.
#A #u1 #u2 #u3 #v #Hu1 #Hu2 #Hu3 #a * #Ha
/3 width=1 by/
qed.

(* Advanced constructions with subset_le ************************************)

lemma subset_le_or_3_dx_sx (A) (v) (u1) (u2) (u3):
      v ⊆ u1 → v ⊆ ∪∪❪A❫ u1 | u2 | u3.
#A #v #u1 #u2 #u3 #Hv
@(subset_le_trans … Hv) //
qed.

lemma subset_le_or_3_dx_rc (A) (v) (u1) (u2) (u3):
      v ⊆ u2 → v ⊆ ∪∪❪A❫ u1 | u2 | u3.
#A #v #u1 #u2 #u3 #Hv
@(subset_le_trans … Hv) //
qed.

lemma subset_le_or_3_dx_dx (A) (v) (u1) (u2) (u3):
      v ⊆ u3 → v ⊆ ∪∪❪A❫ u1 | u2 | u3.
#A #v #u1 #u2 #u3 #Hv
@(subset_le_trans … Hv) //
qed.

(* Main constructions with subset_le ****************************************)

theorem subset_or_3_le_repl (A):
        compatible_4 … (subset_le …) (subset_le …) (subset_le …) (subset_le …) (subset_or_3 A).
#A #u1 #v1 #H1 #u2 #v2 #H2 #u3 #v3 #H3
@subset_le_or_3_sx (**) (* full auto too slow *)
/3 width=1 by subset_le_or_3_dx_refl_sx, subset_le_or_3_dx_refl_rc, subset_le_or_3_dx_refl_dx/
qed.
