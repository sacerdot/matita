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

include "Basic_2/grammar/term.ma".

(* SIMPLE (NEUTRAL) TERMS ***************************************************)

inductive simple: term → Prop ≝
   | simple_atom: ∀I. simple (𝕒{I})
   | simple_flat: ∀I,V,T. simple (𝕗{I} V. T)
.

interpretation "simple (term)" 'Simple T = (simple T).

(* Basic inversion lemmas ***************************************************)

fact simple_inv_bind_aux: ∀T. 𝕊[T] → ∀J,W,U. T = 𝕓{J} W. U → False.
#T * -T
[ #I #J #W #U #H destruct
| #I #V #T #J #W #U #H destruct
]
qed.

lemma simple_inv_bind: ∀I,V,T. 𝕊[𝕓{I} V. T] → False.
/2 width=6/ qed.
