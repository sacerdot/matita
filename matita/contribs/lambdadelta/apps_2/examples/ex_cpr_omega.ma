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

include "basic_2/rt_transition/cpr.ma".

(* EXAMPLES *****************************************************************)

(* A reduction cycle in two steps: the term Omega ***************************)

definition Delta: term → term ≝ λW. +ⓛW.ⓐ#0.#0.

definition Omega1: term → term ≝ λW. ⓐ(Delta W).(Delta W).

definition Omega2: term → term ≝ λW. +ⓓⓝW.(Delta W).ⓐ#0.#0.

(* Basic properties *********************************************************)

lemma Delta_lifts: ∀W1,W2,f. ⬆*[f] W1 ≡ W2 →
                   ⬆*[f] (Delta W1) ≡ (Delta W2).
/4 width=1 by lifts_lref, lifts_bind, lifts_flat/ qed.

(* Main properties **********************************************************)

theorem cpr_Omega_12: ∀h,G,L,W. ⦃G, L⦄ ⊢ Omega1 W ➡[h] Omega2 W.
/2 width=1 by cpm_beta/ qed.

theorem cpr_Omega_21: ∀h,G,L,W. ⦃G, L⦄ ⊢ Omega2 W ➡[h] Omega1 W.
#h #G #L #W1 elim (lifts_total W1 (𝐔❴1❵))
/5 width=5 by lifts_flat, cpm_zeta, cpm_eps, cpm_appl, cpm_delta, Delta_lifts/
qed.
