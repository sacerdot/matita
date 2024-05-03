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

include "ground/subsets/subsets_inhabited_le.ma".
include "ground/subsets/subset_nimply_le.ma".
include "ground/notation/relations/subset_3.ma".
include "ground/notation/relations/not_subset_3.ma".

(* STRICT INCLUSION FOR SUBSETS *********************************************)

definition subset_lt (A): relation2 (𝒫❨A❩) (𝒫❨A❩) ≝
           λu1,u2. ∧∧ u1 ⊆ u2 & u2 ⧵ u1 ϵ ⊙
.

interpretation
  "strict inclusion (subset)"
  'Subset A u1 u2 = (subset_lt A u1 u2).

interpretation
  "negated strict inclusion (subset)"
  'NotSubset A u1 u2 = (negation (subset_lt A u1 u2)).


(* Basic constructions ******************************************************)

lemma subset_lt_mk (A) (u1) (u2):
      u1 ⊆ u2 → u2 ⧵ u1 ϵ ⊙{A} → u1 ⊂ u2.
/2 width=1 by conj/
qed.

lemma subset_lt_le_trans (A) (u:𝒫❨A❩) (u1) (u2):
      u1 ⊂ u → u ⊆ u2 → u1 ⊂ u2.
#A #u #u1 #u2 * #Hu1 #Hu #Hu2
/4 width=5 by subsets_inh_le_repl_fwd, subset_le_nimp_bi, subset_lt_mk/
qed.

lemma subset_le_lt_trans (A) (u:𝒫❨A❩) (u1) (u2):
      u1 ⊆ u → u ⊂ u2 → u1 ⊂ u2.
#A #u #u1 #u2 #Hu1 * #Hu #Hu2
/4 width=5 by subsets_inh_le_repl_fwd, subset_le_nimp_bi, subset_lt_mk/
qed.

(* Basic inversions *********************************************************)

lemma subset_lt_inv_refl (A) (u:𝒫❨A❩): (**)
      u ⊂ u → ⊥.
#A #u * #_ #H0
elim (subsets_inh_inv_in … H0) -H0 #a *
/2 width=1 by/
qed-.

lemma subset_lt_inv_nle (A) (u1) (u2:𝒫❨A❩): (**)
      u1 ⊂ u2 → u2 ⧸⊆ u1.
#A #u1 #u2 #Hu
/3 width=5 by subset_lt_inv_refl, subset_lt_le_trans/
qed-.

(* Basic destructions *******************************************************)

lemma subset_lt_des_le (A) (u1) (u2:𝒫❨A❩): (**)
      u1 ⊂ u2 → u1 ⊆ u2.
#A #u1 #u2 * #Hu #_
//
qed-.

(* Main constructions *******************************************************)

theorem subset_lt_trans (A):
        Transitive … (subset_lt A).
/3 width=3 by subset_lt_des_le, subset_lt_le_trans/
qed.
