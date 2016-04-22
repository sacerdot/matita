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

include "basic_2/computation/fpbg_fpbs.ma".

(* EXAMPLES *****************************************************************)

(* Reflexivity of proper qrst-computation: the term ApplOmega ***************)

definition ApplDelta: term → nat → term ≝ λW,s. +ⓛW.ⓐ⋆s.ⓐ#0.#0.

definition ApplOmega1: term → nat → term ≝ λW,s. ⓐ(ApplDelta W s).(ApplDelta W s).

definition ApplOmega2: term → nat → term ≝ λW,s. +ⓓⓝW.(ApplDelta W s).ⓐ⋆s.ⓐ#0.#0.

definition ApplOmega3: term → nat → term ≝ λW,s. ⓐ⋆s.(ApplOmega1 W s).

(* Basic properties *********************************************************)

lemma ApplDelta_lift: ∀W1,W2,s,l,k. ⬆[l, k] W1 ≡ W2 →
                      ⬆[l, k] (ApplDelta W1 s) ≡ (ApplDelta W2 s).
/5 width=1 by lift_flat, lift_bind, lift_lref_lt/ qed.

lemma cpr_ApplOmega_12: ∀G,L,W,s. ⦃G, L⦄ ⊢ ApplOmega1 W s ➡ ApplOmega2 W s.
/2 width=1 by cpr_beta/ qed.

lemma cpr_ApplOmega_23: ∀G,L,W,s. ⦃G, L⦄ ⊢ ApplOmega2 W s ➡ ApplOmega3 W s.
#G #L #W1 #s elim (lift_total W1 0 1) #W2 #HW12
@(cpr_zeta … (ApplOmega3 W2 s)) /4 width=1 by ApplDelta_lift, lift_flat/
@cpr_flat // @cpr_flat @(cpr_delta … (ApplDelta W1 s) ? 0)
[3,5,8,10: /2 width=2 by ApplDelta_lift/ |4,9: /2 width=1 by cpr_eps/ |*: skip ]
qed.

lemma cpxs_ApplOmega_13: ∀h,o,G,L,W,s. ⦃G, L⦄ ⊢ ApplOmega1 W s ➡*[h,o] ApplOmega3 W s.
/4 width=3 by cpxs_strap1, cpr_cpx/ qed.

lemma fqup_ApplOmega_13: ∀G,L,W,s. ⦃G, L, ApplOmega3 W s⦄ ⊐+ ⦃G, L, ApplOmega1 W s⦄.
/2 width=1 by/ qed.

(* Main properties **********************************************************)

theorem fpbg_refl: ∀h,o,G,L,W,s. ⦃G, L, ApplOmega1 W s⦄ >≡[h,o] ⦃G, L, ApplOmega1 W s⦄.
/3 width=5 by fpbs_fpbg_trans, fqup_fpbg, cpxs_fpbs/ qed.
