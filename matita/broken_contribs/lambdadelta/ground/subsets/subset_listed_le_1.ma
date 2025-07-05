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

include "ground/subsets/subset_listed_le.ma".
include "ground/subsets/subset_listed_1.ma".

(* SUBSET WITH LISTED ELEMENTS **********************************************)

(* Constructions with subset_le *********************************************)

lemma subset_single_le_sn (A) (u) (a):
      a ϵ u → ❴a:A❵ ⊆ u.
#A #u #a #Ha #b #Hb
lapply (subset_in_inv_single ??? Hb) -Hb #H0 destruct //
qed.

(* Inversions with subset_le ************************************************)

lemma subset_le_inv_single_sn (A) (u) (a):
      ❴a:A❵ ⊆ u → a ϵ u.
#A #u #a #Ha
elim (subset_le_inv_listed_lcons_sn ???? Ha) -Ha #Ha #_ //
qed-.
