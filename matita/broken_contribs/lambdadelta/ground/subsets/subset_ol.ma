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

include "ground/subsets/subset.ma".
include "ground/notation/relations/between_3.ma".
include "ground/notation/relations/not_between_3.ma".

(* OVERLAP FOR SUBSETS ******************************************************)

definition subset_ol (A): relation2 (𝒫❨A❩) (𝒫❨A❩) ≝
           λu1,u2. ∃∃p. p ϵ u1 & p ϵ u2.

interpretation
  "overlap (subset)"
  'Between A u1 u2 = (subset_ol A u1 u2).

interpretation
  "negated overlap (subset)"
  'NotBetween A u1 u2 = (negation (subset_ol A u1 u2)).

(* Basic constructions ******************************************************)

lemma subset_ol_i (A) (u1) (u2) (a):
      a ϵ u1 → a ϵ u2 → u1 ≬{A} u2.
/2 width=3 by ex2_intro/ qed.
