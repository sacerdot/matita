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

include "ground/subsets/subset_or_le.ma".
include "ground/subsets/subset_or_3_le.ma".

(* TERNARY UNION FOR SUBSETS ************************************************)

(* Constructions with subset_or and subset_le *******************************)

lemma subset_le_or_or_3_bi (A) (u1) (u2) (u3) (v1) (v2) (v3):
      (∪∪ u1 | u2 | u3) ∪ (∪∪ v1 | v2 | v3) ⊆ ∪∪❪A❫ u1 ∪ v1 | u2 ∪ v2 | (u3 ∪ v3).
#A #u1 #u2 #u3 #v1 #v2 #v3
@subset_le_or_sx @subset_le_or_3_sx
/3 width=3 by subset_le_or_3_dx_rc, subset_le_or_3_dx_sx, subset_or_3_in_dx, subset_le_or_dx_refl_dx, subset_le_or_dx_refl_sx/
qed.

lemma subset_ge_or_or_3_bi (A) (u1) (u2) (u3) (v1) (v2) (v3):
      ∪∪❪A❫ u1 ∪ v1 | u2 ∪ v2 | (u3 ∪ v3) ⊆ (∪∪ u1 | u2 | u3) ∪ (∪∪ v1 | v2 | v3).
#A #u1 #u2 #u3 #v1 #v2 #v3
@subset_le_or_3_sx @subset_le_or_sx
/3 width=3 by subset_le_or_3_dx_refl_dx, subset_le_or_3_dx_refl_rc, subset_le_or_3_dx_refl_sx, subset_le_or_dx_sx, subset_le_or_dx_dx/
qed.
