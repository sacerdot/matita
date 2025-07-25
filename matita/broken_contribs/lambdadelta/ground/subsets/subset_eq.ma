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

include "ground/subsets/subset_le.ma".
include "ground/notation/relations/arroweq_2.ma".

(* EQUIVALENCE FOR SUBSETS **************************************************)

definition subset_eq (A): relation2 (𝒫❨A❩) (𝒫❨A❩) ≝
           λu1,u2. ∧∧ u1 ⊆ u2 & u2 ⊆ u1.

interpretation
  "equivalence (subset)"
  'ArrowEq u1 u2 = (subset_eq ? u1 u2).

(* Basic destructions *******************************************************)

lemma subset_in_eq_repl_back (A) (a:A):
      ∀u1. a ϵ u1 → ∀u2. u2 ⇔ u1 → a ϵ u2.
#A #a #u1 #Hu1 #u2 *
/2 width=1 by/
qed-.

lemma subset_in_eq_repl_fwd (A) (a:A):
      ∀u1. a ϵ u1 → ∀u2. u1 ⇔ u2 → a ϵ u2.
#A #a #u1 #Hu1 #u2 *
/2 width=1 by/
qed-.

lemma subset_in_eq_repl (A):
      replace_2 … (eq …) (subset_eq A) (λa,u. aϵu).
/2 width=3 by subset_in_eq_repl_fwd/
qed-.

(* Basic constructions ******************************************************)

lemma subset_eq_refl (A):
      reflexive … (subset_eq A).
/2 width=1 by conj/
qed.

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

theorem subset_eq_canc_sn (A):
        left_cancellable … (subset_eq A).
/3 width=3 by subset_eq_trans, subset_eq_sym/
qed-.

theorem subset_eq_canc_dx (A):
        right_cancellable … (subset_eq A).
/3 width=3 by subset_eq_trans, subset_eq_sym/
qed-.

theorem subset_eq_repl (A):
        replace_2 … (subset_eq …) (subset_eq …) (subset_eq A).
/3 width=3 by subset_eq_canc_sn, subset_eq_trans/
qed-.
