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

definition ApplDelta: term → nat → term ≝ λW,k. +ⓛW.ⓐ⋆k.ⓐ#0.#0.

definition ApplOmega1: term → nat → term ≝ λW,k. ⓐ(ApplDelta W k).(ApplDelta W k).

definition ApplOmega2: term → nat → term ≝ λW,k. +ⓓⓝW.(ApplDelta W k).ⓐ⋆k.ⓐ#0.#0.

definition ApplOmega3: term → nat → term ≝ λW,k. ⓐ⋆k.(ApplOmega1 W k).

(* Basic properties *********************************************************)

lemma ApplDelta_lift: ∀W1,W2,k,l,m. ⬆[l, m] W1 ≡ W2 →
                      ⬆[l, m] (ApplDelta W1 k) ≡ (ApplDelta W2 k).
/5 width=1 by lift_flat, lift_bind, lift_lref_lt/ qed.

lemma cpr_ApplOmega_12: ∀G,L,W,k. ⦃G, L⦄ ⊢ ApplOmega1 W k ➡ ApplOmega2 W k.
/2 width=1 by cpr_beta/ qed.

lemma cpr_ApplOmega_23: ∀G,L,W,k. ⦃G, L⦄ ⊢ ApplOmega2 W k ➡ ApplOmega3 W k.
#G #L #W1 #k elim (lift_total W1 0 1) #W2 #HW12
@(cpr_zeta … (ApplOmega3 W2 k)) /4 width=1 by ApplDelta_lift, lift_flat/
@cpr_flat // @cpr_flat @(cpr_delta … (ApplDelta W1 k) ? 0)
[3,5,8,10: /2 width=2 by ApplDelta_lift/ |4,9: /2 width=1 by cpr_eps/ |*: skip ]
qed.

lemma cpxs_ApplOmega_13: ∀h,g,G,L,W,k. ⦃G, L⦄ ⊢ ApplOmega1 W k ➡*[h,g] ApplOmega3 W k.
/4 width=3 by cpxs_strap1, cpr_cpx/ qed.

lemma fqup_ApplOmega_13: ∀G,L,W,k. ⦃G, L, ApplOmega3 W k⦄ ⊐+ ⦃G, L, ApplOmega1 W k⦄.
/2 width=1 by/ qed.

(* Main properties **********************************************************)

theorem fpbg_refl: ∀h,g,G,L,W,k. ⦃G, L, ApplOmega1 W k⦄ >≡[h,g] ⦃G, L, ApplOmega1 W k⦄.
/3 width=5 by fpbs_fpbg_trans, fqup_fpbg, cpxs_fpbs/ qed.
