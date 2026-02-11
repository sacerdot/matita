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

(* UNION FOR SUBSETS ********************************************************)

definition subset_or (A) (u1) (u2): 𝒫❨A❩ ≝
           {p | ∨∨ p ϵ u1 | p ϵ u2}.

interpretation
  "union (subset)"
  'union u1 u2 = (subset_or ? u1 u2).

(* Basic constructions ******************************************************)

lemma subset_or_in_sx (A) (u1) (u2) (p):
      p ϵ u1 → p ϵ❪A❫ u1 ∪ u2.
/2 width=1 by or_introl/
qed.

lemma subset_or_in_dx (A) (u1) (u2) (p):
      p ϵ u2 → p ϵ❪A❫ u1 ∪ u2.
/2 width=1 by or_intror/
qed.

(* Basic inversions *********************************************************)

lemma subset_nin_or (A) (a) (u1) (u2):
      a ⧸ϵ u1 → a ⧸ϵ u2 → a ⧸ϵ❪A❫ u1 ∪ u2.
#A #a #u1 #u2 #Hna1 #Hna2 * #Hna
/2 width=1 by/
qed-.

(* Advanced constructions ***************************************************)

lemma subset_in_or_dec (A) (a) (u1) (u2):
      Decidable (a ϵ u1) →
      Decidable (a ϵ u2) →
      Decidable (a ϵ❪A❫ u1∪u2).
#A #a #u1 #u2 * #Ha1 [ #_ | * #Ha2 ]
[ /3 width=1 by subset_or_in_sx, or_introl/
| /3 width=1 by subset_or_in_dx, or_introl/
| /4 width=7 by subset_nin_or, or_intror/
]
qed-.

lemma subset_nin_inv_or_sx (A) (a) (u1) (u2):
      a ⧸ϵ❪A❫ u1 ∪ u2 → a ⧸ϵ u1.
#A #a #u1 #u2 #Hna #Ha
/3 width=1 by subset_or_in_sx/
qed-.

lemma subset_nin_inv_or_dx (A) (a) (u1) (u2):
      a ⧸ϵ❪A❫ u1 ∪ u2 → a ⧸ϵ u2.
#A #a #u1 #u2 #Hna #Ha
/3 width=1 by subset_or_in_dx/
qed-.
