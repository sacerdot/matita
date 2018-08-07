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

include "basic_2/rt_computation/fpbs_cpxs.ma".
include "basic_2/rt_computation/fpbg_fqup.ma".
include "basic_2/rt_computation/fpbg_fpbs.ma".

(* EXAMPLES *****************************************************************)

(* Reflexivity of proper rst-computation: the term ApplOmega ****************)

definition ApplDelta: term → nat → term ≝ λW,s. +ⓛW.ⓐ⋆s.ⓐ#0.#0.

definition ApplOmega1: term → nat → term ≝ λW,s. ⓐ(ApplDelta W s).(ApplDelta W s).

definition ApplOmega2: term → nat → term ≝ λW,s. +ⓓⓝW.(ApplDelta W s).ⓐ⋆s.ⓐ#0.#0.

definition ApplOmega3: term → nat → term ≝ λW,s. ⓐ⋆s.(ApplOmega1 W s).

(* Basic properties *********************************************************)

lemma ApplDelta_lifts (f:rtmap):
                      ∀W1,W2,s. ⬆*[f] W1 ≘ W2 →
                      ⬆*[f] (ApplDelta W1 s) ≘ (ApplDelta W2 s).
/5 width=1 by lifts_sort, lifts_lref, lifts_bind, lifts_flat/ qed.

lemma cpr_ApplOmega_12 (h): ∀G,L,W,s. ⦃G, L⦄ ⊢ ApplOmega1 W s ➡[h] ApplOmega2 W s.
/2 width=1 by cpm_beta/ qed.

lemma cpr_ApplOmega_23 (h): ∀G,L,W,s. ⦃G, L⦄ ⊢ ApplOmega2 W s ➡[h] ApplOmega3 W s.
#h #G #L #W1 #s elim (lifts_total W1 (𝐔❴1❵)) #W2 #HW12
@(cpm_zeta … (ApplOmega3 W2 s)) /4 width=1 by ApplDelta_lifts, lifts_flat/
@cpm_appl // @cpm_appl @(cpm_delta … (ApplDelta W1 s))
/2 width=1 by ApplDelta_lifts, cpm_eps/
qed.

lemma cpxs_ApplOmega_13 (h): ∀G,L,W,s. ⦃G, L⦄ ⊢ ApplOmega1 W s ⬈*[h] ApplOmega3 W s.
/4 width=4 by cpxs_strap1, cpm_fwd_cpx/ qed.

lemma fqup_ApplOmega_13: ∀G,L,W,s. ⦃G, L, ApplOmega3 W s⦄ ⊐+ ⦃G, L, ApplOmega1 W s⦄.
/2 width=1 by/ qed.

(* Main properties **********************************************************)

theorem fpbg_refl (h) (o): ∀G,L,W,s. ⦃G, L, ApplOmega1 W s⦄ >[h,o] ⦃G, L, ApplOmega1 W s⦄.
/3 width=5 by fpbs_fpbg_trans, fqup_fpbg, cpxs_fpbs/ qed.
