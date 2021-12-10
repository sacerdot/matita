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

include "ground/notation/relations/white_harrow_2.ma".
include "ground/lib/subset_inclusion.ma".

(* EQUIVALENCE FOR SUBSETS **************************************************)

definition subset_eq (A): relation2 𝒫❨A❩ 𝒫❨A❩ ≝
           λu1,u2. ∧∧ u1 ⊆ u2 & u2 ⊆ u1.

interpretation
  "equivalence (subset)"
  'WhiteHArrow u1 u2 = (subset_eq ? u1 u2).

(* Basic constructions ******************************************************)

lemma subset_eq_refl (A):
      reflexive … (subset_eq A).
/2 width=1 by conj/ qed.

lemma subset_eq_sym (A):
      symmetric … (subset_eq A).
#A #u1 #u2 * /2 width=1 by conj/
qed-.

(* Main constructions *******************************************************)

theorem subset_eq_trans (A):
        Transitive … (subset_eq A).
#A #u1 #u2 * #H12 #H21 #u3 * #H23 #H32
/3 width=5 by subset_le_trans, conj/
qed-.
