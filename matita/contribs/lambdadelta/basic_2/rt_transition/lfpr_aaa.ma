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

include "basic_2/rt_transition/lfpx_aaa.ma".
include "basic_2/rt_transition/lfpr_lfpx.ma".

(* PARALLEL R-TRANSITION FOR LOCAL ENV.S ON REFERRED ENTRIES ****************)

(* Properties with atomic arity assignment for terms ************************)

lemma cpr_aaa_conf: ∀h,G,L,T1,A. ⦃G, L⦄ ⊢ T1 ⁝ A →
                    ∀T2. ⦃G, L⦄ ⊢ T1 ➡[h] T2 → ⦃G, L⦄ ⊢ T2 ⁝ A.
/3 width=5 by cpx_aaa_conf, cpm_fwd_cpx/ qed-.

lemma lfpr_aaa_conf: ∀h,G,L1,T,A. ⦃G, L1⦄ ⊢ T ⁝ A →
                     ∀L2. ⦃G, L1⦄ ⊢ ➡[h, T] L2 → ⦃G, L2⦄ ⊢ T ⁝ A.
/3 width=4 by lfpx_aaa_conf, lfpr_fwd_lfpx/ qed-.
