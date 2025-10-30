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
include "ground/subsets/subset_nimply.ma".

(* DIFFERENCE FOR SUBSETS ***************************************************)

(* Constructions with subset_le *********************************************)

lemma subset_le_nimp_sx_refl_sx (A) (u1) (u2):
      u1 ⧵{A} u2 ⊆ u1.
#A #u1 #u2 #a * #Hu1 #_ //
qed.

lemma subset_le_nimp_bi (A) (u1) (u2) (v1) (v2):
      u1 ⊆ v1 → u2 ⊆ v2 → u1 ⧵ v2 ⊆ v1 ⧵{A} u2.
#A #u1 #u2 #v1 #v2 #H1 #H2 #a * #Hu1 #Hv2
/4 width=1 by subset_in_nimp/
qed.
