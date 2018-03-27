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

include "basic_2/rt_transition/cpx_ffdeq.ma".
include "basic_2/rt_computation/lpxs_cpxs.ma".
include "basic_2/rt_computation/fpbs_lpxs.ma".

(* PARALLEL RST-COMPUTATION FOR CLOSURES ************************************)

(* Properties with uncounted context-sensitive parallel rt-transition *******)

(* Basic_2A1: uses: fpbs_cpx_trans_neq *)
lemma fpbs_cpx_tdneq_trans: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄ →
                            ∀U2. ⦃G2, L2⦄ ⊢ T2 ⬈[h] U2 → (T2 ≛[h, o] U2 → ⊥) →
                            ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ⬈[h] U1 & T1 ≛[h, o] U1 → ⊥ & ⦃G1, L1, U1⦄ ≥[h, o] ⦃G2, L2, U2⦄.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H #U2 #HTU2 #HnTU2
elim (fpbs_inv_star … H) -H #G0 #L0 #L3 #T0 #T3 #HT10 #H10 #HL03 #H32
elim (ffdeq_cpx_trans … H32 … HTU2) -HTU2 #T4 #HT34 #H42
lapply (ffdeq_tdneq_repl_dx … H32 … H42 … HnTU2) -T2 #HnT34
lapply (lpxs_cpx_trans … HT34 … HL03) -HT34 #HT34
elim (fqus_cpxs_trans_tdneq … H10 … HT34 HnT34) -T3 #T2 #HT02 #HnT02 #H24
elim (tdeq_dec h o T1 T0) [ #H10 | -HnT02 #HnT10 ]
[ lapply (cpxs_trans … HT10 … HT02) -HT10 -HT02 #HT12
  elim (cpxs_tdneq_fwd_step_sn … o … HT12) [2: /3 width=3 by tdeq_canc_sn/ ] -T0 -HT12
| elim (cpxs_tdneq_fwd_step_sn … HT10 … HnT10) -HT10 -HnT10
]
/4 width=16 by fpbs_intro_star, cpxs_tdeq_fpbs_trans, ex3_intro/
qed-.
