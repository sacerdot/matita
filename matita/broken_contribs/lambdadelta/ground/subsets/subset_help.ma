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

(* SUBSETS ******************************************************************)

(* Help constructions *******************************************************)

lemma subset_le_help_1 (A) (u1) (u2) (v1) (v2:𝒫❨A❩): (**)
      (u1 ∪ v1) ∪ (u2 ∪ v2) ⊆ (u1 ∪ u2) ∪ (v1 ∪ v2).
#A #u1 #u2 #v1 #v2 #a * * #Ha
/3 width=1 by subset_or_in_dx, subset_or_in_sx/
qed.
