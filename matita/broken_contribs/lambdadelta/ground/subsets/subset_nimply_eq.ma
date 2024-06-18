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
include "ground/subsets/subset_nimply_le.ma".

(* DIFFERENCE FOR SUBSETS ***************************************************)

(* Constructions with subset_eq *********************************************)

lemma subset_nimp_eq_repl (A) (u1) (u2) (v1) (v2):
      u1 ⇔ v1 → u2 ⇔ v2 → u1 ⧵ u2 ⇔ v1 ⧵{A} v2.
#A #u1 #u2 #v1 #v2 * #Huv1 #Hvu1 * #Huv2 #Hvu2
@conj @subset_le_nimp_bi //
qed.
