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

include "static_2/static/feqx.ma".
include "basic_2/rt_transition/cpx_reqx.ma".
include "basic_2/rt_transition/rpx_reqx.ma".

(* EXTENDED CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS **************)

(* Properties with sort-irrelevant equivalence for closures *****************)

(**) (* to update *)
lemma feqx_cpx_trans:
      ∀G1,G2,L1,L2,T1,T. ❪G1,L1,T1❫ ≛ ❪G2,L2,T❫ →
      ∀T2. ❪G2,L2❫ ⊢ T ⬈ T2 →
      ∃∃T0. ❪G1,L1❫ ⊢ T1 ⬈ T0 & ❪G1,L1,T0❫ ≛ ❪G2,L2,T2❫.
#G1 #G2 #L1 #L2 #T1 #T #H #T2 #HT2
elim (feqx_inv_gen_dx … H) -H #H #HL12 #HT1 destruct
lapply (reqx_cpx_trans … HL12 … HT2) #H
lapply (cpx_reqx_conf_dx … HT2 … HL12) -HT2 -HL12 #HL12
lapply (teqx_cpx_trans … HT1 … H) -T #HT12
/3 width=3 by feqx_intro_dx, ex2_intro/
qed-.
