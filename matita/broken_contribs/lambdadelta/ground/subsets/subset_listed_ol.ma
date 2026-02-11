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

include "ground/subsets/subset_ol.ma".
include "ground/subsets/subset_listed.ma".

(* SUBSET WITH LISTED ELEMENTS **********************************************)

(* Inversions with subset_ol ************************************************)

lemma subset_nol_empty_sx (A) (u2):
      (Ⓕ) ⧸≬❪A❫ u2.
#A #u2 * #a #Ha #_
/2 width=3 by subset_nin_inv_empty/
qed-.
