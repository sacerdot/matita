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

include "ground/xoa/sum_2.ma".
include "ground/subsets/subset.ma".
include "ground/notation/functions/sq_cup_4.ma".

(* SUM FOR SUBSETS **********************************************************)

definition subset_sum (A1) (A2) (u1) (u2): 𝒫❨++A1|A2❩ ≝
           {a | match a with
                [ in_1_2 a1 ⇒ a1 ϵ u1
                | in_2_2 a2 ⇒ a2 ϵ u2
                ]
           }.

interpretation
  "sum (subset)"
  'SqCup A1 A2 u1 u2 = (subset_sum A1 A2 u1 u2).

(* Basic constructions ******************************************************)

lemma subset_in_sum_sn (A1) (A2) (u1) (u2) (a):
      a ϵ u1 → in_1_2 A1 A2 a ϵ u1 ⊔ u2.
#A1 #A2 #u1 #u2 #a #Ha //
qed.

lemma subset_in_sum_dx (A1) (A2) (u1) (u2) (a):
      a ϵ u2 → in_2_2 A1 A2 a ϵ u1 ⊔ u2.
#A1 #A2 #u1 #u2 #a #Ha //
qed.

(* Basic inversions *********************************************************)

lemma subset_in_inv_sum_sn (A1) (A2) (u1) (u2) (a1):
      in_1_2 A1 A2 a1 ϵ u1 ⊔ u2 → a1 ϵ u1.
// qed-.

lemma subset_in_inv_sum_dx (A1) (A2) (u1) (u2) (a2):
      in_2_2 A1 A2 a2 ϵ u1 ⊔ u2 → a2 ϵ u2.
// qed-.
