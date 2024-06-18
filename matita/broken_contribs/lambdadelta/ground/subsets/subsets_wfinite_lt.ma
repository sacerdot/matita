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

include "ground/subsets/subset_listed_lt.ma".
include "ground/subsets/subsets_wfinite.ma".

(* WEAKLY FINITE SUBSETS ****************************************************)

(* Eliminations with subset_lt **********************************************)

lemma subsets_wfinite_ind_lt_le (A:Type[0]) (Q:predicate …): (**)
      (∀a1,a2. Decidable … (a1 ={A} a2)) →
      (∀u2. u2 ϵ 𝐖𝛀 → (∀u1. u1 ⊂ u2 → Q u1) → Q u2) →
      ∀u2. u2 ϵ 𝐖𝛀{A} → ∀u1. u1 ⊆ u2 → Q u1.
#A #Q #HA #IH0 #u2 * #l2
generalize in match u2; -u2
@(subset_listed_ind_lt ?? HA ? l2) -l2
#l2 #IH #u2 #Hul2 #u1 #Hu12
lapply (subset_le_trans ??? Hu12 ? Hul2) -Hul2 #Hul
@IH0 -IH0 [ /2 width=2 by subsets_wfinite_in/ ] #u0 #Hu01
elim (subset_lt_des_listed_dx … u0 l2 HA)
[| /2 width=6 by subset_lt_le_trans/ ] #l0 #Hul0 #Hl02 #_
/2 width=5 by/
qed-.

lemma subsets_wfinite_ind_lt (A:Type[0]) (Q:predicate …): (**)
      (∀a1,a2. Decidable … (a1 ={A} a2)) →
      (∀u2. u2 ϵ 𝐖𝛀 → (∀u1. u1 ⊂ u2 → Q u1) → Q u2) →
      ∀u2. u2 ϵ 𝐖𝛀{A} → Q u2.
#A #Q #HA #IH #u2 #Hu2
@(subsets_wfinite_ind_lt_le … HA IH … Hu2 u2) -Q -HA -Hu2 //
qed-.
