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

include "ground/notation/relations/doteq_4.ma".
include "ground/lib/relations.ma".

(* EXTENSIONAL EQUIVALENCE **************************************************)

definition exteq (A,B:Type[0]): relation (A → B) ≝
           λf1,f2. ∀a. f1 a = f2 a.

interpretation
  "extensional equivalence"
  'DotEq A B f1 f2 = (exteq A B f1 f2).

(* Basic constructions ******************************************************)

lemma exteq_refl (A) (B): reflexive … (exteq A B).
// qed.

lemma exteq_repl (A) (B): replace_2 … (exteq A B) (exteq A B) (exteq A B).
// qed-.

lemma exteq_sym (A) (B): symmetric … (exteq A B).
/2 width=1 by exteq_repl/ qed-.

lemma exteq_trans (A) (B): Transitive … (exteq A B).
/2 width=1 by exteq_repl/ qed-.

lemma exteq_canc_sn (A) (B): left_cancellable … (exteq A B).
/2 width=1 by exteq_repl/ qed-.

lemma exteq_canc_dx (A) (B): right_cancellable … (exteq A B).
/2 width=1 by exteq_repl/ qed-.

(* Constructions with function composition **********************************)

lemma compose_repl_fwd_dx (A) (B) (C) (g) (f1) (f2):
      f1 ≐{A,B} f2 → g ∘ f1 ≐{A,C} g ∘ f2.
#A #B #C #g #f1 #f2 #Hf12 #a
whd in ⊢ (??%%); //
qed.

lemma compose_repl_bak_dx (A) (B) (C) (g) (f1) (f2):
      f1 ≐{A,B} f2 → g ∘ f2 ≐{A,C} g ∘ f1.
/3 width=1 by compose_repl_fwd_dx, exteq_sym/
qed.

lemma compose_repl_fwd_sn (A) (B) (C) (g1) (g2) (f):
      g1 ≐{B,C} g2 → g1 ∘ f ≐{A,C} g2 ∘ f.
#A #B #C #g1 #g2 #f #Hg12 #a
whd in ⊢ (??%%); //
qed.

lemma compose_repl_bak_sn (A) (B) (C) (g1) (g2) (f):
      g1 ≐{B,C} g2 → g2 ∘ f ≐{A,C} g1 ∘ f.
/3 width=1 by compose_repl_fwd_sn, exteq_sym/
qed.

lemma compose_assoc (A1) (A2) (A3) (A4) (f3:A3→A4) (f2:A2→A3) (f1:A1→A2):
      f3 ∘ (f2 ∘ f1) ≐ f3 ∘ f2 ∘ f1.
// qed.
