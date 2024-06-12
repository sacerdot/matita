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
include "ground/notation/functions/backslash_3.ma".

(* DIFFERENCE FOR SUBSETS ***************************************************)

definition subset_nimp (A) (u1) (u2): 𝒫❨A❩ ≝
           {a | ∧∧ a ϵ u1 & a ⧸ϵ u2}.

interpretation
  "difference (subset)"
  'Backslash A u1 u2 = (subset_nimp A u1 u2).

(* Basic constructions ******************************************************)

lemma subset_nimply_in (A) (u1) (u2) (a):
      a ϵ u1 → a ⧸ϵ u2 → a ϵ{A} u1 ⧵ u2.
/2 width=1 by conj/
qed.

(* Main constructions *******************************************************)

theorem subset_in_nimp_nimp_bi (A) (u) (v1) (v2) (a):
        a ϵ u → a ϵ v2 ⧵ v1 → a ϵ (u ⧵ v1) ⧵{A} (u ⧵ v2).
#A #u #v1 #v2 #a #Hu * #Hv2 #Hnv1
@subset_nimply_in
[ /2 width=1 by subset_nimply_in/
| * /2 width=1 by/
]
qed.
