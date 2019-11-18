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

include "static_2/s_transition/fqu_teqx.ma".
include "static_2/static/feqx.ma".
include "basic_2/rt_transition/fpb_reqx.ma".

(* PROPER PARALLEL RST-TRANSITION FOR CLOSURES ******************************)

(* Properties with degree-based equivalence for closures ********************)

(* Basic_2A1: uses: fleq_fpb_trans *)
lemma feqx_fpb_trans: ∀h,F1,F2,K1,K2,T1,T2. ⦃F1,K1,T1⦄ ≛ ⦃F2,K2,T2⦄ →
                      ∀G2,L2,U2. ⦃F2,K2,T2⦄ ≻[h] ⦃G2,L2,U2⦄ →
                      ∃∃G1,L1,U1. ⦃F1,K1,T1⦄ ≻[h] ⦃G1,L1,U1⦄ & ⦃G1,L1,U1⦄ ≛ ⦃G2,L2,U2⦄.
#h #F1 #F2 #K1 #K2 #T1 #T2 * -F2 -K2 -T2
#K2 #T2 #HK12 #HT12 #G2 #L2 #U2 #H12
elim (teqx_fpb_trans … HT12 … H12) -T2 #K0 #T0 #H #HT0 #HK0
elim (reqx_fpb_trans … HK12 … H) -K2 #L0 #U0 #H #HUT0 #HLK0
@(ex2_3_intro … H) -H (**) (* full auto too slow *)
/4 width=3 by feqx_intro_dx, reqx_trans, teqx_reqx_conf, teqx_trans/
qed-.

(* Inversion lemmas with degree-based equivalence for closures **************)

(* Basic_2A1: uses: fpb_inv_fleq *)
lemma fpb_inv_feqx: ∀h,G1,G2,L1,L2,T1,T2. ⦃G1,L1,T1⦄ ≻[h] ⦃G2,L2,T2⦄ →
                    ⦃G1,L1,T1⦄ ≛ ⦃G2,L2,T2⦄ → ⊥.
#h #G1 #G2 #L1 #L2 #T1 #T2 * -G2 -L2 -T2
[ #G2 #L2 #T2 #H12 #H elim (feqx_inv_gen_sn … H) -H
  /3 width=11 by reqx_fwd_length, fqu_inv_teqx/
| #T2 #_ #HnT #H elim (feqx_inv_gen_sn … H) -H /2 width=1 by/
| #L2 #_ #HnL #H elim (feqx_inv_gen_sn … H) -H /2 width=1 by/
]
qed-.
