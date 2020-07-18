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

include "static_2/static/req.ma".
include "basic_2/rt_transition/rpx_lpx.ma".

(* EXTENDED PARALLEL RT-TRANSITION FOR FULL LOCAL ENVIRONMENTS **************)

(* Properties with generic equivalence for local environments ***************)

lemma reqg_lpx_trans_rpx (S) (G) (L) (T:term):
      ∀L1. L1 ≛[S,T] L → ∀L2. ❪G,L❫ ⊢ ⬈ L2 → ❪G,L❫ ⊢ ⬈[T] L2.
/3 width=1 by lpx_rpx, reqg_rpx_trans/ qed.

(* Basic_2A1: uses: lleq_lpx_trans *)
lemma reqg_lpx_trans (S) (G) (T:term):
      reflexive … S → symmetric … S →
      ∀L2,K2. ❪G,L2❫ ⊢ ⬈ K2 → ∀L1. L1 ≛[S,T] L2 →
      ∃∃K1. ❪G,L1❫ ⊢ ⬈ K1 & K1 ≛[S,T] K2.
#S #G #T #H1S #H2S #L2 #K2 #HLK2 #L1 #HL12
lapply (lpx_rpx … T … HLK2) -HLK2 #HLK2
lapply (reqg_rpx_trans … HL12 … HLK2) -L2 // #H
elim (rpx_fwd_lpx_req … H) -H #K1 #HLK1 #HK12
/3 width=3 by req_fwd_reqg, ex2_intro/
qed-.

(* Inversion lemmas with sort-irrelevant equivalence for local environments *)

lemma rpx_inv_reqg_lpx (S) (G) (T):
      reflexive … S →
      ∀L1,L2. ❪G,L1❫ ⊢ ⬈[T] L2 →
      ∃∃L. L1 ≛[S,T] L & ❪G,L❫ ⊢ ⬈ L2.
#S #G #T #HS #L1 #L2 #H
elim (rpx_inv_req_lpx … H) -H #L #HL1 #HL2
/3 width=3 by req_fwd_reqg, ex2_intro/
qed-.

(* Forward lemmas with sort-irrelevant equivalence for local environments ***)

lemma rpx_fwd_lpx_reqg (S) (G) (T):
      reflexive … S →
      ∀L1,L2. ❪G,L1❫ ⊢ ⬈[T] L2 →
      ∃∃L. ❪G,L1❫ ⊢ ⬈ L & L ≛[S,T] L2.
#S #G #T #HS #L1 #L2 #H
elim (rpx_fwd_lpx_req … H) -H #L #HL1 #HL2
/3 width=3 by req_fwd_reqg, ex2_intro/
qed-.
