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

include "basic_2/reduction/cpr.ma".

(* EXAMPLES *****************************************************************)

(* A reduction cycle in two steps: the term Omega ***************************)

definition Delta: term ≝ +ⓛ⋆0.ⓐ#0.#0.

definition Omega1: term ≝ ⓐDelta.Delta.

definition Omega2: term ≝ +ⓓⓝ⋆0.Delta.ⓐ#0.#0.

(* Basic properties *********************************************************)

lemma Delta_lift: ∀d,e. ⇧[d, e] Delta ≡ Delta.
/4 width=1 by lift_flat, lift_bind, lift_lref_lt/ qed.

(* Main properties **********************************************************)

theorem cpr_Omega_12: ⦃⋆, ⋆⦄ ⊢ Omega1 ➡ Omega2.
/2 width=1 by cpr_beta/ qed.

theorem cpr_Omega_21: ⦃⋆, ⋆⦄ ⊢ Omega2 ➡ Omega1.
@(cpr_zeta … Omega1) /2 width=1 by lift_flat/
@cpr_flat @(cpr_delta … Delta ? 0)
[3,5,8,10: // |4,9: /2 width=1 by cpr_eps/ |*: skip ]
qed.
