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

include "static_2/static/rex_lex.ma".
include "basic_2/rt_transition/rpx_reqg.ma".
include "basic_2/rt_transition/lpx.ma".

(* EXTENDED PARALLEL RT-TRANSITION FOR REFERRED LOCAL ENVIRONMENTS **********)

(* Properties with syntactic equivalence for referred local environments ****)

lemma req_rpx (G) (T):
      ∀L1,L2. L1 ≡[T] L2 → ❪G,L1❫ ⊢ ⬈[T] L2.
/2 width=1 by req_fwd_rex/ qed.

(* Properties with extended rt-transition for full local envs ***************)

lemma lpx_rpx (G) (T):
      ∀L1,L2. ❪G,L1❫ ⊢ ⬈ L2 → ❪G,L1❫ ⊢ ⬈[T] L2.
/2 width=1 by rex_lex/ qed.

(* Inversion lemmas with extended rt-transition for full local envs *********)

lemma rpx_inv_req_lpx (G) (T):
      ∀L1,L2. ❪G,L1❫ ⊢ ⬈[T] L2 →
      ∃∃L. L1 ≡[T] L & ❪G,L❫ ⊢ ⬈ L2.
/4 width=13 by cpx_reqg_conf, rex_inv_req_lex, rex_conf1_next/ qed-.

(* Forward lemmas with extended rt-transition for full local envs ***********)

lemma rpx_fwd_lpx_req (G) (T):
      ∀L1,L2. ❪G,L1❫ ⊢ ⬈[T] L2 →
      ∃∃L. ❪G,L1❫ ⊢ ⬈ L & L ≡[T] L2.
/3 width=3 by rpx_fsge_comp, rex_fwd_lex_req/ qed-.
