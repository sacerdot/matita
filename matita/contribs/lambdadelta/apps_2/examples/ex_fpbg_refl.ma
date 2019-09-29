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

definition ApplDelta (s0) (s): term ≝ +ⓛ⋆s0.ⓐ⋆s.ⓐ#0.#0.

definition ApplOmega1 (s0) (s): term ≝ ⓐ(ApplDelta s0 s).(ApplDelta s0 s).

definition ApplOmega2 (s0) (s): term ≝ +ⓓⓝ⋆s0.(ApplDelta s0 s).ⓐ⋆s.ⓐ#0.#0.

definition ApplOmega3 (s0) (s): term ≝ +ⓓⓝ⋆s0.(ApplDelta s0 s).ⓐ⋆s.(ApplOmega1 s0 s).

definition ApplOmega4 (s0) (s): term ≝ ⓐ⋆s.(ApplOmega1 s0 s).

(* Basic properties *********************************************************)

lemma ApplDelta_lifts (f:rtmap) (s0) (s):
                      ⇧*[f] (ApplDelta s0 s) ≘ (ApplDelta s0 s).
/5 width=1 by lifts_sort, lifts_lref, lifts_bind, lifts_flat/ qed.

lemma cpr_ApplOmega_12 (h) (G) (L) (s0) (s): ⦃G,L⦄ ⊢ ApplOmega1 s0 s ➡[h] ApplOmega2 s0 s.
/2 width=1 by cpm_beta/ qed.

lemma cpr_ApplOmega_23 (h) (G) (L) (s0) (s): ⦃G,L⦄ ⊢ ApplOmega2 s0 s ➡[h] ApplOmega3 s0 s.
/6 width=3 by cpm_eps, cpm_appl, cpm_bind, cpm_delta, ApplDelta_lifts/ qed.

lemma cpr_ApplOmega_34 (h) (G) (L) (s0) (s): ⦃G,L⦄ ⊢ ApplOmega3 s0 s ➡[h] ApplOmega4 s0 s.
/4 width=3 by cpm_zeta, ApplDelta_lifts, lifts_sort, lifts_flat/ qed.

lemma cpxs_ApplOmega_14 (h) (G) (L) (s0) (s): ⦃G,L⦄ ⊢ ApplOmega1 s0 s ⬈*[h] ApplOmega4 s0 s.
/5 width=4 by cpxs_strap1, cpm_fwd_cpx/ qed.

lemma fqup_ApplOmega_41 (G) (L) (s0) (s): ⦃G,L,ApplOmega4 s0 s⦄ ⬂+ ⦃G,L,ApplOmega1 s0 s⦄.
/2 width=1 by/ qed.

(* Main properties **********************************************************)

theorem fpbg_refl (h) (G) (L) (s0) (s): ⦃G,L,ApplOmega1 s0 s⦄ >[h] ⦃G,L,ApplOmega1 s0 s⦄.
/3 width=5 by fpbs_fpbg_trans, fqup_fpbg, cpxs_fpbs/ qed.
