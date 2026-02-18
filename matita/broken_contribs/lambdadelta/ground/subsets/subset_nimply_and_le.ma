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
include "ground/subsets/subset_and.ma".
include "ground/subsets/subset_nimply.ma".

(* DIFFERENCE FOR SUBSETS ***************************************************)

(* Constructions with subset_and and subset_le ******************************)

lemma subset_ge_nimp_and_sx_assoc_sx (A) (u1) (u2) (v): (**)
      (u1 ⧵ v) ∩ u2 ⊆ (u1 ∩ u2) ⧵❪A❫ v.
#A #u1 #u2 #v #a * * #H1a #Hna #H2a
/3 width=1 by subset_and_in/
qed.
