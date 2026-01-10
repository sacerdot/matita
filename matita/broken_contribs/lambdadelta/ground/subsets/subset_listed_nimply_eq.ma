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
include "ground/subsets/subset_listed_nimply_le.ma".

(* SUBSET WITH LISTED ELEMENTS **********************************************)

(* Constructions with subset_eq *********************************************)

lemma subset_eq_empty_nimp (A) (u1) (u2):
      u1 ⊆ u2 → Ⓕ ⇔ u1 ⧵❪A❫ u2.
#A #u1 #u2 #Hu @conj [ // ]
#a * #H1a #H2a elim H2a -H2a
/2 width=1/
qed.

lemma subset_eq_nimp_dx_refl_empty (A) (u1):
      u1 ⇔ u1 ⧵❪A❫ Ⓕ.
#A #u2 @conj [| // ]
/3 width=3 by subset_nin_inv_empty, subset_in_nimp/
qed.

lemma subset_eq_nimp_dx_empty_refl (A) (u2):
      (Ⓕ) ⇔ Ⓕ ⧵❪A❫ u2.
#A #u2 @conj //
qed.
