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

include "ground/subsets/subset_or.ma".
include "ground/subsets/subset_rest_le.ma".

(* RESTRICTION FOR SUBSETS **************************************************)

(* Basic constructions with subset_or and subset_le *************************)

lemma subset_rest_or_ge (A) (R) (u1) (u2): (**)
      (❨R❩u1) ∪ (❨R❩u2) ⊆ ❨R❩❪A❫(u1 ∪ u2).
#A #R #u1 #u2 #a * * #x #Ha
/3 width=1 by subset_and_in, subset_or_in_dx, subset_or_in_sx/
qed.

lemma subset_rest_or_le (A) (R) (u1) (u2): (**)
      ❨R❩❪A❫(u1 ∪ u2) ⊆ (❨R❩u1) ∪ (❨R❩u2).
#A #R #u1 #u2 #a * #x * #Ha
/3 width=1 by subset_and_in, subset_or_in_dx, subset_or_in_sx/
qed.
