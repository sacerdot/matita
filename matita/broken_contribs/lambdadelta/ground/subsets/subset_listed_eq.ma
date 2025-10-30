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
include "ground/subsets/subset_listed_le.ma".

(* SUBSET WITH LISTED ELEMENTS **********************************************)

(* Constructions with subset_eq *********************************************)

lemma subset_eq_empty_sx (A) (u):
      u ⊆ Ⓕ → Ⓕ{A} ⇔ u.
#A #u @conj //
qed.
