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

(* INTERSECTION FOR SUBSETS *************************************************)

definition subset_and (A) (u1) (u2): 𝒫❨A❩ ≝
           {p | ∧∧ p ϵ u1 & p ϵ u2}.

interpretation
  "intersection (subset)"
  'intersects u1 u2 = (subset_and ? u1 u2).

(* Basic constructions ******************************************************)

lemma subset_and_in (A) (u1) (u2) (p):
      p ϵ u1 → p ϵ u2 → p ϵ❪A❫ u1 ∩ u2.
/2 width=1 by conj/
qed.

(* Negated constructions ****************************************************)

lemma subset_nin_and_dx (A) (u1) (u2) (p):
      p ⧸ϵ u1 → p ⧸ϵ❪A❫ u1 ∩ u2.
#A #u1 #u2 #a #Hna * #H1a #_
/2 width=1/
qed-.

lemma subset_nin_and_sx (A) (u1) (u2) (p):
      p ⧸ϵ u2 → p ⧸ϵ❪A❫ u1 ∩ u2.
#A #u1 #u2 #a #Hna * #_ #H2a
/2 width=1/
qed-.

(* Negated inversions *******************************************************)

lemma subset_nin_inv_and (A) (u1) (u2) (p):
      (∨∨ Decidable (p ϵ u1) | Decidable (p ϵ u2)) →
      p ⧸ϵ❪A❫ u1 ∩ u2 → ∨∨ p ⧸ϵ u1 | p ⧸ϵ u2.
#A #u1 #u2 #a * * #H0 #Hna
[ /4 width=1 by subset_and_in, or_intror/
| /2 width=1 by or_introl/
| /4 width=1 by subset_and_in, or_introl/
| /2 width=1 by or_intror/
]
qed-.
