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

include "ground/subsets/subset_ol_le.ma".
include "ground/subsets/subset_and_le.ma".

(* INTERSECTION FOR SUBSETS *************************************************)

(* Constructions with subset_ol *********************************************)

(* Note: overlap algebra: preservation of infimum *)
lemma subset_ol_and_dx_refl_sx (A) (u1) (u2):
      u1 ≬ u2 → u1 ≬❪A❫ (u1 ∩ u2).
#A #u1 #u2 * #p #H1 #H2
/3 width=4 by subset_and_in, subset_ol_i/
qed.

(* Note: overlap algebra: preservation of infimum *)
lemma subset_ol_and_sx_refl_dx (A) (u1) (u2):
      u1 ≬ u2 → (u1 ∩ u2) ≬❪A❫ u2.
#A #u1 #u2 * #p #H1 #H2
/3 width=4 by subset_and_in, subset_ol_i/
qed.

lemma subset_ol_and_sx (A) (u) (v1) (v2):
      (u ∩ v1) ≬ v2 → (u ∩ v1) ≬❪A❫ (u ∩ v2).
#A #u #v1 #v2 * #a * #Hu #Hv1 #Hv2
/3 width=4 by subset_ol_i, subset_and_in/
qed.

(* Inversions with subset_ol ************************************************)

lemma subset_ol_inv_and_dx_refl_sx (A) (u1) (u2):
      u1 ≬❪A❫ (u1 ∩ u2) → u1 ≬ u2.
#A #u1 #u2 #H0
@(subset_ol_le_repl … H0) -H0 //
qed-.

lemma subset_ol_inv_and_sx_refl_dx (A) (u1) (u2):
      (u1 ∩ u2) ≬❪A❫ u2 → u1 ≬ u2.
#A #u1 #u2 #H0
@(subset_ol_le_repl … H0) -H0 //
qed-.
