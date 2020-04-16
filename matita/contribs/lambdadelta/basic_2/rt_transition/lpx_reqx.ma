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

include "static_2/static/reqx_req.ma".
include "basic_2/rt_transition/rpx_reqx.ma".
include "basic_2/rt_transition/rpx_lpx.ma".

(* EXTENDED PARALLEL RT-TRANSITION FOR FULL LOCAL ENVIRONMENTS **************)

(* Properties with sort-irrelevant equivalence for local environments *******)

(* Basic_2A1: uses: lleq_lpx_trans *)
lemma reqx_lpx_trans (G):
      ∀L2,K2. ❪G,L2❫ ⊢ ⬈ K2 → ∀L1. ∀T:term. L1 ≛[T] L2 →
      ∃∃K1. ❪G,L1❫ ⊢ ⬈ K1 & K1 ≛[T] K2.
#G #L2 #K2 #HLK2 #L1 #T #HL12
lapply (lpx_rpx … T HLK2) -HLK2 #HLK2
elim (reqx_rpx_trans … HLK2 … HL12) -L2 #K #H #HK2
elim (rpx_inv_lpx_req … H) -H #K1 #HLK1 #HK1
/3 width=5 by req_reqx_trans, ex2_intro/
qed-.
