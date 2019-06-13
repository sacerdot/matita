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
include "basic_2/rt_transition/rpx_fsle.ma".
include "basic_2/rt_transition/lpx.ma".

(* UNBOUND PARALLEL RT-TRANSITION FOR REFERRED LOCAL ENVIRONMENTS ***********)

(* Properties with syntactic equivalence for referred local environments ****)

lemma fleq_rpx (h) (G): ∀L1,L2,T. L1 ≡[T] L2 → ⦃G,L1⦄ ⊢ ⬈[h,T] L2.
/2 width=1 by req_fwd_rex/ qed.

(* Properties with unbound parallel rt-transition for full local envs *******)

lemma lpx_rpx: ∀h,G,L1,L2,T. ⦃G,L1⦄ ⊢ ⬈[h] L2 → ⦃G,L1⦄ ⊢ ⬈[h,T] L2.
/2 width=1 by rex_lex/ qed.

(* Inversion lemmas with unbound parallel rt-transition for full local envs *)

lemma rpx_inv_lpx_req: ∀h,G,L1,L2,T. ⦃G,L1⦄ ⊢ ⬈[h,T] L2 →
                       ∃∃L. ⦃G,L1⦄ ⊢ ⬈[h] L & L ≡[T] L2.
/3 width=3 by rpx_fsge_comp, rex_inv_lex_req/ qed-.
