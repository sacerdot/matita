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

include "static_2/s_transition/fqu_teqg.ma".
include "static_2/static/feqg.ma".
include "basic_2/rt_transition/fpb_reqg.ma".

(* PROPER PARALLEL RST-TRANSITION FOR CLOSURES ******************************)

(* Properties with generic equivalence for closures *************************)

(* Basic_2A1: uses: fleq_fpb_trans *)
lemma feqg_fpb_trans (S):
      reflexive … S → symmetric … S → Transitive … S →
      ∀F1,F2,K1,K2,T1,T2. ❪F1,K1,T1❫ ≛[S] ❪F2,K2,T2❫ →
      ∀G2,L2,U2. ❪F2,K2,T2❫ ≻ ❪G2,L2,U2❫ →
      ∃∃G1,L1,U1. ❪F1,K1,T1❫ ≻ ❪G1,L1,U1❫ & ❪G1,L1,U1❫ ≛[S] ❪G2,L2,U2❫.
#S #H1S #H2S #H3S #F1 #F2 #K1 #K2 #T1 #T2 * -F2 -K2 -T2
#K2 #T2 #HK12 #HT12 #G2 #L2 #U2 #H12
elim (teqg_fpb_trans … HT12 … H12) -T2 // #K0 #T0 #H #HT0 #HK0
elim (reqg_fpb_trans … HK12 … H) -K2 // #L0 #U0 #H #HUT0 #HLK0
@(ex2_3_intro … H) -H (**) (* full auto too slow *)
/4 width=5 by feqg_intro_dx, reqg_trans, teqg_reqg_conf_sn, teqg_trans/
qed-.

(* Inversion lemmas with generic equivalence for closures *******************)

(* Basic_2A1: uses: fpb_inv_fleq *)
lemma fpb_inv_feqg (S):
      ∀G1,G2,L1,L2,T1,T2. ❪G1,L1,T1❫ ≻ ❪G2,L2,T2❫ →
      ❪G1,L1,T1❫ ≛[S] ❪G2,L2,T2❫ → ⊥.
#S #G1 #G2 #L1 #L2 #T1 #T2 * -G2 -L2 -T2
[ #G2 #L2 #T2 #H12 #H elim (feqg_inv_gen_sn … H) -H
  /3 width=11 by reqg_fwd_length, fqu_inv_teqg/
| #T2 #_ #HnT #H elim (feqg_inv_gen_sn … H) -H /3 width=2 by teqg_teqx/
| #L2 #_ #HnL #H elim (feqg_inv_gen_sn … H) -H /3 width=2 by reqg_reqx/
]
qed-.
