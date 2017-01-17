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

include "basic_2/rt_transition/lfpx.ma".
include "basic_2/rt_transition/cpm_cpx.ma".
include "basic_2/rt_transition/lfpr.ma".

(* PARALLEL R-TRANSITION FOR LOCAL ENV.S ON REFERRED ENTRIES ****************)

(* Fwd. lemmas with unc. rt-transition for local env.s on referred entries **)

lemma lfpx_frees_conf_fwd_lfpr: ∀h,G. lexs_frees_confluent (cpx h G) cfull →
                                lexs_frees_confluent (cpm 0 h G) cfull.
/4 width=7 by cpm_fwd_cpx, lexs_co/ qed-.

lemma lfpr_fwd_lfpx: ∀h,T,G,L1,L2. ⦃G, L1⦄ ⊢ ➡[h, T] L2 → ⦃G, L1⦄ ⊢ ⬈[h, T] L2.
/3 width=3 by cpm_fwd_cpx, lfxs_co/ qed-.
