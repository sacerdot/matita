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

include "ground/lib/subset.ma".

(* INCLUSION FOR SUBSETS ****************************************************)

definition subset_le (A): relation2 (𝒫❨A❩) (𝒫❨A❩) ≝
           λu1,u2. ∀p. p ϵ u1 → p ϵ u2.

interpretation
  "inclusion (subset)"
  'subseteq u1 u2 = (subset_le ? u1 u2).

(* Basic constructions ******************************************************)

lemma subset_le_refl (A):
      reflexive … (subset_le A).
// qed.

(* Main constructions *******************************************************)

theorem subset_le_trans (A):
        Transitive … (subset_le A).
/3 width=1 by/ qed-.
