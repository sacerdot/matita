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

include "ground/notation/functions/negrightarrow_2.ma".
include "ground/lib/bool.ma".

(* EXCLUSIVE DISJUNCTION FOR BOOLEANS ***************************************)

definition bminus (b1) (b2): bool ≝
  b1 ∧ ¬b2.

interpretation
  "negated implication (booleans)"
  'NegRightArrow b1 b2 = (bminus b1 b2).

(* Basic constructions ******************************************************)

lemma bninus_false_sx (b):
      ⓕ = ⓕ ↛ b.
// qed.

lemma bninus_true_false:
      ⓣ = ⓣ ↛ ⓕ.
// qed.

lemma bninus_true_bi:
      ⓕ = ⓣ ↛ ⓣ.
// qed.
