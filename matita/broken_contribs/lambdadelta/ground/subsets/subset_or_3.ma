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

include "ground/xoa/or_3.ma".
include "ground/subsets/subset.ma".
include "ground/notation/functions/union_4.ma".

(* TERNARY UNION FOR SUBSETS ************************************************)

definition subset_or_3 (A) (u1) (u2) (u3): 𝒫❨A❩ ≝
           {p | ∨∨ p ϵ u1 | p ϵ u2 | p ϵ u3}.

interpretation
  "ternary union (subset)"
  'Union A u1 u2 u3 = (subset_or_3 A u1 u2 u3).

(* Basic constructions ******************************************************)

lemma subset_or_3_in_sx (A) (u1) (u2) (u3) (a):
      a ϵ u1 → a ϵ❪A❫ ∪∪ u1 | u2 | u3.
/2 width=1 by or3_intro0/
qed.

lemma subset_or_3_in_rc (A) (u1) (u2) (u3) (a):
      a ϵ u2 → a ϵ❪A❫ ∪∪ u1 | u2 | u3.
/2 width=1 by or3_intro1/
qed.

lemma subset_or_3_in_dx (A) (u1) (u2) (u3) (a):
      a ϵ u3 → a ϵ❪A❫ ∪∪ u1 | u2 | u3.
/2 width=1 by or3_intro2/
qed.
