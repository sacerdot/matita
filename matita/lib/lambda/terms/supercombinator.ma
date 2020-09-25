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

include "lambda/terms/term.ma".

(* SUPERCOMBINATOR **********************************************************)

inductive is_supercombinator: nat → nat → predicate term ≝
| is_supercombinator_vref:
  ∀i,d. i < d → ∀h. is_supercombinator h d (#i)
| is_supercombinator_abst:
  ∀A,h. is_supercombinator (S h) (S h) A → ∀d. is_supercombinator h d (𝛌.A)
| is_supercombinator_appl:
  ∀B,A,d. is_supercombinator 0 d B → is_supercombinator 0 d A →
  ∀h. is_supercombinator h d (@B.A)
.
