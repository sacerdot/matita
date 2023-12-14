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

(* UNION FOR SUBSETS ********************************************************)

definition subset_or (A) (u1) (u2): 𝒫❨A❩ ≝
           λp. ∨∨ p ϵ u1 | p ϵ u2.

interpretation
  "union (subset)"
  'union u1 u2 = (subset_or ? u1 u2).

(* Basic constructions ******************************************************)

lemma subset_or_in_sn (A) (u1) (u2) (p):
      p ϵ u1 → p ϵ{A} u1 ∪ u2.
/2 width=1 by or_introl/
qed.

lemma subset_or_in_dx (A) (u1) (u2) (p):
      p ϵ u2 → p ϵ{A} u1 ∪ u2.
/2 width=1 by or_intror/
qed.
