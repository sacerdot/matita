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

include "ground/subsets/subset_nimply.ma".
include "ground/subsets/subset_rest_le.ma".

(* RESTRICTION FOR SUBSETS **************************************************)

(* Basic constructions with subset_nimply and subset_le *********************)

lemma subset_rest_nimp_ge (A) (R) (u) (v): (**)
      (❨R❩u)⧵v ⊆ ❨R❩❪A❫(u⧵v).
#A #R #u #v #a * * #H1a #H2a #Hna
/4 width=1 by subset_in_nimp, subset_and_in/
qed.

lemma subset_rest_nimp_le (A) (R) (u) (v): (**)
      ❨R❩❪A❫(u⧵v) ⊆ (❨R❩u)⧵v.
#A #R #u #v #a * #H1a * #H2a #Hna
/4 width=1 by subset_in_nimp, subset_and_in/
qed.
