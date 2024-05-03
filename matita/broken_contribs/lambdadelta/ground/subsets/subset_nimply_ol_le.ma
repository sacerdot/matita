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
include "ground/subsets/subset_ol.ma".
include "ground/subsets/subset_nimply.ma".

(* DIFFERENCE FOR SUBSETS ***************************************************)

(* Constructions with subset_ol and subset_le *******************************)

lemma subset_le_nimp_dx_refl_sn_fwd (A) (u1) (u2):
      u1 ⧸≬{A} u2 → u1 ⊆ u1 ⧵ u2.
#A #u1 #u2 #Hu #a #Hu1
/4 width=3 by subset_nimply_in, subset_ol_i/
qed.

lemma subset_le_nimp_dx_refl_sn_rev (A) (u1) (u2):
      u2 ⧸≬{A} u1 → u1 ⊆ u1 ⧵ u2.
#A #u1 #u2 #Hu #a #Hu1
/4 width=3 by subset_nimply_in, subset_ol_i/
qed.
