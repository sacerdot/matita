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

include "basic_2/static/ffdeq.ma".
include "basic_2/rt_transition/cpx_lfdeq.ma".
include "basic_2/rt_transition/lfpx_lfdeq.ma".

(* UNCOUNTED CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS *************)

(* Properties with degree-based equivalence for closures ********************)

lemma ffdeq_cpx_trans: ∀h,o,G1,G2,L1,L2,T1,T. ⦃G1, L1, T1⦄ ≛[h, o] ⦃G2, L2, T⦄ →
                       ∀T2. ⦃G2, L2⦄ ⊢ T ⬈[h] T2 →
                       ∃∃T0. ⦃G1, L1⦄ ⊢ T1 ⬈[h] T0 & ⦃G1, L1, T0⦄ ≛[h, o] ⦃G2, L2, T2⦄.
#h #o #G1 #G2 #L1 #L2 #T1 #T #H #T2 #HT2
elim (ffdeq_inv_gen_dx … H) -H #H #HL12 #HT1 destruct
elim (lfdeq_cpx_trans … HL12 … HT2) #T0 #HT0 #HT02
lapply (cpx_lfdeq_conf_dx … HT2 … HL12) -HL12 #HL12
elim (tdeq_cpx_trans … HT1 … HT0) -T #T #HT1 #HT0
/4 width=5 by ffdeq_intro_dx, tdeq_trans, ex2_intro/
qed-.
