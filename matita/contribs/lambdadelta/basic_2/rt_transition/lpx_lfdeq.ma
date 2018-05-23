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

include "basic_2/static/lfdeq_lfeq.ma".
include "basic_2/rt_transition/lfpx_lfdeq.ma".
include "basic_2/rt_transition/lfpx_lpx.ma".

(* UNBOUND PARALLEL RT-TRANSITION FOR FULL LOCAL ENVIRONMENTS ***************)

(* Properties with degree-based equivalence for local environments **********)

(* Basic_2A1: uses: lleq_lpx_trans *)
lemma lfdeq_lpx_trans (h) (o) (G): ∀L2,K2. ⦃G, L2⦄ ⊢ ⬈[h] K2 →
                                   ∀L1. ∀T:term. L1 ≛[h, o, T] L2 →
                                   ∃∃K1. ⦃G, L1⦄ ⊢ ⬈[h] K1 & K1 ≛[h, o, T] K2.
#h #o #G #L2 #K2 #HLK2 #L1 #T #HL12
lapply (lpx_lfpx … T HLK2) -HLK2 #HLK2
elim (lfdeq_lfpx_trans … HLK2 … HL12) -L2 #K #H #HK2
elim (lfpx_inv_lpx_lfeq … H) -H #K1 #HLK1 #HK1
/3 width=5 by lfeq_lfdeq_trans, ex2_intro/
qed-.
