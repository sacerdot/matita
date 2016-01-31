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

include "basic_2/notation/relations/simple_1.ma".
include "basic_2/grammar/term.ma".

(* SIMPLE (NEUTRAL) TERMS ***************************************************)

inductive simple: predicate term ≝
   | simple_atom: ∀I. simple (⓪{I})
   | simple_flat: ∀I,V,T. simple (ⓕ{I} V. T)
.

interpretation "simple (term)" 'Simple T = (simple T).

(* Basic inversion lemmas ***************************************************)

fact simple_inv_bind_aux: ∀T. 𝐒⦃T⦄ → ∀p,J,W,U. T = ⓑ{p,J}W.U → ⊥.
#T * -T
[ #I #p #J #W #U #H destruct
| #I #V #T #a #J #W #U #H destruct
]
qed-.

lemma simple_inv_bind: ∀p,I,V,T. 𝐒⦃ⓑ{p,I} V. T⦄ → ⊥.
/2 width=7 by simple_inv_bind_aux/ qed-.

lemma simple_inv_pair: ∀I,V,T.  𝐒⦃②{I}V.T⦄ → ∃J. I = Flat2 J.
* /2 width=2 by ex_intro/
#p #I #V #T #H elim (simple_inv_bind … H)
qed-.
