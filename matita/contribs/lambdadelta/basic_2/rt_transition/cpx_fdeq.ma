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

include "static_2/static/fdeq.ma".
include "basic_2/rt_transition/cpx_rdeq.ma".
include "basic_2/rt_transition/rpx_rdeq.ma".

(* UNBOUND CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS ***************)

(* Properties with degree-based equivalence for closures ********************)

lemma fdeq_cpx_trans: ∀h,o,G1,G2,L1,L2,T1,T. ⦃G1, L1, T1⦄ ≛[h, o] ⦃G2, L2, T⦄ →
                      ∀T2. ⦃G2, L2⦄ ⊢ T ⬈[h] T2 →
                      ∃∃T0. ⦃G1, L1⦄ ⊢ T1 ⬈[h] T0 & ⦃G1, L1, T0⦄ ≛[h, o] ⦃G2, L2, T2⦄.
#h #o #G1 #G2 #L1 #L2 #T1 #T #H #T2 #HT2
elim (fdeq_inv_gen_dx … H) -H #H #HL12 #HT1 destruct
elim (rdeq_cpx_trans … HL12 … HT2) #T0 #HT0 #HT02
lapply (cpx_rdeq_conf_dx … HT2 … HL12) -HL12 #HL12
elim (tdeq_cpx_trans … HT1 … HT0) -T #T #HT1 #HT0
/4 width=5 by fdeq_intro_dx, tdeq_trans, ex2_intro/
qed-.
