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

include "ground/subsets/subset_eq.ma".
include "ground/subsets/subset_or.ma".
include "ground/subsets/subset_nimply.ma".

(* DIFFERENCE FOR SUBSETS ***************************************************)

(* Constructions with subset_or and subset_eq *******************************)

lemma subset_nimp_or_sx (A) (u1) (u2) (u):
      (u1 ⧵ u) ∪ (u2 ⧵ u) ⇔ (u1 ∪ u2) ⧵❪A❫ u.
#A #u1 #u2 #u @conj #a * * #H1a #H2a
/3 width=1 by subset_in_nimp, subset_or_in_dx, subset_or_in_sx/
qed.

lemma subset_eq_or_dx (A) (u) (u1) (u2):
      u2 ⊆ u1 → (∀a:A.Decidable (aϵu2)) →
      u1 ⧵❪A❫ u2 ⇔ u → u1 ⇔ u2 ∪ u.
#A #u #u1 #u2 #H1u #H2u * #Hu1 #Hu2
@conj #a [ elim (H2u a) #H2a | * ] #H1a
[ /2 width=1 by subset_or_in_sx/
| /5 width=1 by subset_in_nimp, subset_or_in_dx/
| /2 width=1 by/
| lapply (Hu2 … H1a) -u * #Ha #_ //
]
qed.
