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
