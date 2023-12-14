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

(* INTERSECTION FOR SUBSETS *************************************************)

definition subset_and (A) (u1) (u2): 𝒫❨A❩ ≝
           λp. ∧∧ p ϵ u1 & p ϵ u2.

interpretation
  "intersection (subset)"
  'intersects u1 u2 = (subset_and ? u1 u2).

(* Basic constructions ******************************************************)

lemma subset_and_in (A) (u1) (u2) (p):
      p ϵ u1 → p ϵ u2 → p ϵ{A} u1 ∩ u2.
/2 width=1 by conj/
qed.
