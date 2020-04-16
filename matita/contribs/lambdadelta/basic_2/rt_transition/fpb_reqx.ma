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

include "static_2/static/reqx_fqus.ma".
include "basic_2/rt_transition/cpx_reqx.ma".
include "basic_2/rt_transition/lpx_reqx.ma".
include "basic_2/rt_transition/fpb.ma".

(* PROPER PARALLEL RST-TRANSITION FOR CLOSURES ******************************)

(* Properties with sort-irrelevant equivalence for local environments *******)

lemma teqx_fpb_trans:
      ∀U2,U1. U2 ≛ U1 →
      ∀G1,G2,L1,L2,T1. ❪G1,L1,U1❫ ≻ ❪G2,L2,T1❫ →
      ∃∃L,T2. ❪G1,L1,U2❫ ≻ ❪G2,L,T2❫ & T2 ≛ T1 & L ≛[T1] L2.
#U2 #U1 #HU21 #G1 #G2 #L1 #L2 #T1 * -G2 -L2 -T1
[ #G2 #L2 #T1 #H
  elim (teqx_fqu_trans … H … HU21) -H
  /3 width=5 by fpb_fqu, ex3_2_intro/
| #T1 #HUT1 #HnUT1
  elim (teqx_cpx_trans … HU21 … HUT1) -HUT1
  /6 width=5 by fpb_cpx, teqx_canc_sn, teqx_trans, ex3_2_intro/
| /6 width=5 by fpb_lpx, rpx_teqx_div, teqx_reqx_conf, ex3_2_intro/
]
qed-.

(* Basic_2A1: was just: lleq_fpb_trans *)
lemma reqx_fpb_trans:
      ∀F,K1,K2,T. K1 ≛[T] K2 →
      ∀G,L2,U. ❪F,K2,T❫ ≻ ❪G,L2,U❫ →
      ∃∃L1,U0. ❪F,K1,T❫ ≻ ❪G,L1,U0❫ & U0 ≛ U & L1 ≛[U] L2.
#F #K1 #K2 #T #HT #G #L2 #U * -G -L2 -U
[ #G #L2 #U #H2 elim (reqx_fqu_trans … H2 … HT) -K2
  /3 width=5 by fpb_fqu, ex3_2_intro/
| #U #HTU #HnTU elim (reqx_cpx_trans … HT … HTU) -HTU
  /5 width=11 by fpb_cpx, cpx_reqx_conf_sn, teqx_trans, teqx_reqx_conf, ex3_2_intro/ (**) (* time: 36s on dev *)
| #L2 #HKL2 #HnKL2 elim (reqx_lpx_trans … HKL2 … HT) -HKL2
  /6 width=5 by fpb_lpx, (* 2x *) reqx_canc_sn, ex3_2_intro/
]
qed-.
