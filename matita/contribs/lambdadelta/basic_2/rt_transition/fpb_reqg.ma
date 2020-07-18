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

include "static_2/static/reqg_fqus.ma".
include "basic_2/rt_transition/cpx_reqg.ma".
include "basic_2/rt_transition/lpx_reqg.ma".
include "basic_2/rt_transition/fpb.ma".

(* PROPER PARALLEL RST-TRANSITION FOR CLOSURES ******************************)

(* Properties with generic equivalence for local environments ***************)

lemma teqg_fpb_trans (S):
      reflexive … S → symmetric … S →
      ∀U2,U1. U2 ≛[S] U1 →
      ∀G1,G2,L1,L2,T1. ❪G1,L1,U1❫ ≻ ❪G2,L2,T1❫ →
      ∃∃L,T2. ❪G1,L1,U2❫ ≻ ❪G2,L,T2❫ & T2 ≛[S] T1 & L ≛[S,T1] L2.
#S #H1S #H2S #U2 #U1 #HU21 #G1 #G2 #L1 #L2 #T1 * -G2 -L2 -T1
[ #G2 #L2 #T1 #H
  elim (teqg_fqu_trans … H … HU21) -H
  /3 width=5 by fpb_fqu, ex3_2_intro/
| #T1 #HUT1 #HnUT1
  lapply (teqg_cpx_trans … HU21 … HUT1) -HUT1
  /6 width=5 by fpb_cpx, reqg_refl, teqg_teqx, teqg_canc_sn, teqg_refl, ex3_2_intro/
| /5 width=5 by fpb_lpx, teqg_reqg_conf_sn, reqg_refl, ex3_2_intro/
]
qed-.

(* Basic_2A1: was just: lleq_fpb_trans *)
lemma reqg_fpb_trans (S):
      reflexive … S → symmetric … S →
      ∀F,K1,K2,T. K1 ≛[S,T] K2 →
      ∀G,L2,U. ❪F,K2,T❫ ≻ ❪G,L2,U❫ →
      ∃∃L1,U0. ❪F,K1,T❫ ≻ ❪G,L1,U0❫ & U0 ≛[S] U & L1 ≛[S,U] L2.
#S #H1S #H2S #F #K1 #K2 #T #HT #G #L2 #U * -G -L2 -U
[ #G #L2 #U #H2 elim (reqg_fqu_trans … H2 … HT) -K2
  /3 width=5 by fpb_fqu, ex3_2_intro/
| #U #HTU #HnTU lapply (reqg_cpx_trans … HT … HTU) -HTU //
  /4 width=8 by fpb_cpx, cpx_reqg_conf_sn, teqg_refl, ex3_2_intro/
| #L2 #HKL2 #HnKL2 elim (reqg_lpx_trans … HKL2 … HT) -HKL2 //
  /6 width=9 by fpb_lpx, reqg_reqx, reqg_repl, teqg_refl, ex3_2_intro/
]
qed-.
