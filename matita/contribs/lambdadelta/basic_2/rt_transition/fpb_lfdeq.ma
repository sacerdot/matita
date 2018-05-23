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

include "basic_2/static/lfdeq_fqus.ma".
include "basic_2/rt_transition/cpx_lfdeq.ma".
include "basic_2/rt_transition/lpx_lfdeq.ma".
include "basic_2/rt_transition/fpb.ma".

(* PROPER PARALLEL RST-TRANSITION FOR CLOSURES ******************************)

(* Properties with degree-based equivalence for local environments **********)

lemma tdeq_fpb_trans: ∀h,o,U2,U1. U2 ≛[h, o] U1 →
                      ∀G1,G2,L1,L2,T1. ⦃G1, L1, U1⦄ ≻[h, o] ⦃G2, L2, T1⦄ → 
                      ∃∃L,T2. ⦃G1, L1, U2⦄ ≻[h, o] ⦃G2, L, T2⦄ & T2 ≛[h, o] T1 & L ≛[h, o, T1] L2.
#h #o #U2 #U1 #HU21 #G1 #G2 #L1 #L2 #T1 * -G2 -L2 -T1
[ #G2 #L2 #T1 #H
  elim (tdeq_fqu_trans … H … HU21) -H
  /3 width=5 by fpb_fqu, ex3_2_intro/
| #T1 #HUT1 #HnUT1
  elim (tdeq_cpx_trans … HU21 … HUT1) -HUT1
  /6 width=5 by fpb_cpx, tdeq_canc_sn, tdeq_trans, ex3_2_intro/
| /6 width=5 by fpb_lpx, lfpx_tdeq_div, tdeq_lfdeq_conf, ex3_2_intro/
]
qed-.

(* Basic_2A1: was just: lleq_fpb_trans *)
lemma lfdeq_fpb_trans: ∀h,o,F,K1,K2,T. K1 ≛[h, o, T] K2 →
                       ∀G,L2,U. ⦃F, K2, T⦄ ≻[h, o] ⦃G, L2, U⦄ →
                       ∃∃L1,U0. ⦃F, K1, T⦄ ≻[h, o] ⦃G, L1, U0⦄ & U0 ≛[h, o] U & L1 ≛[h, o, U] L2.
#h #o #F #K1 #K2 #T #HT #G #L2 #U * -G -L2 -U
[ #G #L2 #U #H2 elim (lfdeq_fqu_trans … H2 … HT) -K2
  /3 width=5 by fpb_fqu, ex3_2_intro/
| #U #HTU #HnTU elim (lfdeq_cpx_trans … HT … HTU) -HTU
  /5 width=10 by fpb_cpx, cpx_lfdeq_conf_sn, tdeq_trans, tdeq_lfdeq_conf, ex3_2_intro/
| #L2 #HKL2 #HnKL2 elim (lfdeq_lpx_trans … HKL2 … HT) -HKL2
  /6 width=5 by fpb_lpx, (* 2x *) lfdeq_canc_sn, ex3_2_intro/
]
qed-.
