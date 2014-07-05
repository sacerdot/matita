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

definition Delta: term → term ≝ λW. +ⓛW.ⓐ#0.#0.

definition Omega1: term → term ≝ λW. ⓐ(Delta W).(Delta W).

definition Omega2: term → term ≝ λW. +ⓓⓝW.(Delta W).ⓐ#0.#0.

(* Basic properties *********************************************************)

lemma Delta_lift: ∀W1,W2,d,e. ⇧[d, e] W1 ≡ W2 →
                  ⇧[d, e] (Delta W1) ≡ (Delta W2).
/4 width=1 by lift_flat, lift_bind, lift_lref_lt/ qed.

(* Main properties **********************************************************)

theorem cpr_Omega_12: ∀W. ⦃⋆, ⋆⦄ ⊢ Omega1 W ➡ Omega2 W.
/2 width=1 by cpr_beta/ qed.

theorem cpr_Omega_21: ∀W. ⦃⋆, ⋆⦄ ⊢ Omega2 W ➡ Omega1 W.
#W1 elim (lift_total W1 0 1) #W2 #HW12
@(cpr_zeta … (Omega1 W2)) /3 width=1 by Delta_lift, lift_flat/
@cpr_flat @(cpr_delta … (Delta W1) ? 0)
[3,5,8,10: /2 width=2 by Delta_lift/ |4,9: /2 width=1 by cpr_eps/ |*: skip ]
qed.
