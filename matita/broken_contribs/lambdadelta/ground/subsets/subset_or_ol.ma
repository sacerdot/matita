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
include "ground/subsets/subset_or.ma".

(* UNION FOR SUBSETS ********************************************************)

(* Inversions with subset_ol ************************************************)

(* Note: overlap algebra: splitting of supremum *)
lemma subset_ol_or_inv_sn (A) (u1) (u2) (u:𝒫❨A❩): (**)
      (u1 ∪ u2) ≬ u → ∨∨ u1 ≬ u | u2 ≬ u.
#A #u1 #u2 #u * #p * #H1 #H2
/3 width=3 by subset_ol_i, or_introl, or_intror/
qed-.

(* Constructions with subset_ol *********************************************)

lemma subset_ol_or_sn_sn (A) (u1) (u2) (u:𝒫❨A❩): (**)
      u1 ≬ u → (u1 ∪ u2) ≬ u.
#A #u1 #u2 #u * #p #H1p #H2p
/3 width=3 by subset_or_in_sn, subset_ol_i/
qed.

lemma subset_ol_or_sn_dx (A) (u1) (u2) (u:𝒫❨A❩): (**)
      u2 ≬ u → (u1 ∪ u2) ≬ u.
#A #u1 #u2 #u * #p #H1p #H2p
/3 width=3 by subset_or_in_dx, subset_ol_i/
qed.
