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
include "ground/subsets/subset_and.ma".
include "ground/subsets/subset_nimply.ma".

(* DIFFERENCE FOR SUBSETS ***************************************************)

(* Constructions with subset_and and subset_or and subset_le ****************)

lemma subset_le_or_dx_and_nimp_refl_sx_bi (A) (u) (v):
      (∀a. Decidable (a ϵ❪A❫ v)) →
      u ⊆ (u ∩ v) ∪ (u ⧵ v).
#A #u #v #Hu #a #Ha
elim (Hu a) #Hna
[ /3 width=1 by subset_or_in_sx, subset_and_in/
| /4 width=1 by subset_in_nimp, subset_or_in_dx/
]
qed.

lemma subset_le_or_sx_and_nimp_refl_sx_bi (A) (u) (v):
      (∀a. Decidable (a ϵ❪A❫ v)) →
      (u ∩ v) ∪ (u ⧵ v) ⊆ u.
#A #u #v #Hu #a * * //
qed.
