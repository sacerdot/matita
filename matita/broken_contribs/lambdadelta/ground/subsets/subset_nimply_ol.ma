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
include "ground/subsets/subset_nimply.ma".

(* DIFFERENCE FOR SUBSETS ***************************************************)

(* Constructions with subset_ol *********************************************)

lemma subset_ol_nimp_sn (A) (u1) (u2) (u):
      u1 ≬ u → u2 ⧸≬ u → (u1⧵u2) ≬{A} u.
#A #u1 #u2 #u * #p #H1p #H2p #Hnu
/5 width=3 by subset_in_nimp, subset_ol_i/
qed.

(* Inversions with subset_ol *************************************************)

lemma subset_nol_nimp_sn_refl_dx (A) (u1) (u2):
      u1 ⧵ u2 ⧸≬{A} u2.
#A #u1 #u2 * #a * #_ #Hnu2 #Hu2 -u1
/2 width=1 by/
qed-.
