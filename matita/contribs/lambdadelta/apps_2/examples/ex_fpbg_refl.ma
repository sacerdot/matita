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

include "basic_2/rt_computation/fpbg_fqup.ma".
include "basic_2/rt_computation/fpbs_cpxs.ma".
include "basic_2/rt_computation/fpbg_fpbs.ma".

(* EXAMPLES *****************************************************************)

(* Reflexivity of proper rst-computation: the term ApplOmega ****************)

definition ApplDelta (s0) (s): term ≝ +ⓛ⋆s0.ⓐ⋆s.ⓐ#0.#0.

definition ApplOmega1 (s0) (s): term ≝ ⓐ(ApplDelta s0 s).(ApplDelta s0 s).

definition ApplOmega2 (s0) (s): term ≝ +ⓓⓝ⋆s0.(ApplDelta s0 s).ⓐ⋆s.ⓐ#0.#0.

definition ApplOmega3 (s0) (s): term ≝ +ⓓⓝ⋆s0.(ApplDelta s0 s).ⓐ⋆s.(ApplOmega1 s0 s).

definition ApplOmega4 (s0) (s): term ≝ ⓐ⋆s.(ApplOmega1 s0 s).

(* Basic properties *********************************************************)

lemma ApplDelta_lifts (f) (s0) (s):
      ⇧*[f] (ApplDelta s0 s) ≘ (ApplDelta s0 s).
/5 width=1 by lifts_sort, lifts_lref, lifts_bind, lifts_flat/ qed.

lemma cpr_ApplOmega_12 (G) (L) (s0) (s):
      ❪G,L❫ ⊢ ApplOmega1 s0 s ⬈ ApplOmega2 s0 s.
/2 width=1 by cpx_beta/ qed.

lemma cpr_ApplOmega_23 (G) (L) (s0) (s):
      ❪G,L❫ ⊢ ApplOmega2 s0 s ⬈ ApplOmega3 s0 s.
/6 width=3 by cpx_eps, cpx_flat, cpx_bind, cpx_delta, ApplDelta_lifts/ qed.

lemma cpr_ApplOmega_34 (G) (L) (s0) (s):
      ❪G,L❫ ⊢ ApplOmega3 s0 s ⬈ ApplOmega4 s0 s.
/4 width=3 by cpx_zeta, ApplDelta_lifts, lifts_sort, lifts_flat/ qed.

lemma cpxs_ApplOmega_14 (G) (L) (s0) (s):
      ❪G,L❫ ⊢ ApplOmega1 s0 s ⬈* ApplOmega4 s0 s.
/5 width=5 by cpxs_strap1, cpx_cpxs/ qed.

lemma fqup_ApplOmega_41 (G) (L) (s0) (s):
      ❪G,L,ApplOmega4 s0 s❫ ⬂+ ❪G,L,ApplOmega1 s0 s❫.
/2 width=1 by/ qed.

(* Main properties **********************************************************)

theorem fpbg_refl (G) (L) (s0) (s):
        ❪G,L,ApplOmega1 s0 s❫ > ❪G,L,ApplOmega1 s0 s❫.
/3 width=5 by fpbs_fpbg_trans, fqup_fpbg, cpxs_fpbs/ qed.
