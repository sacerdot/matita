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

include "basic_2/rt_transition/rpx_lpx.ma".
include "basic_2/rt_transition/fpb.ma".

(* PARALLEL RST-TRANSITION FOR CLOSURES *************************************)

(* Properties with extended rt-transition for full local envs ***************)

(* Basic_2A1: uses: fpbq_lpx *)
lemma lpx_fpb (G) (T):
      ∀L1,L2. ❨G,L1❩ ⊢ ⬈ L2 → ❨G,L1,T❩ ≽ ❨G,L2,T❩.
/3 width=1 by rpx_fpb, lpx_rpx/ qed.

lemma fpb_intro_req (G1) (G2) (L1) (L2) (T1) (T2):
      ∀L0,L,T. ❨G1,L1,T1❩ ⬂⸮ ❨G2,L,T❩ → ❨G2,L❩ ⊢ T ⬈ T2 → 
      L ≡[T] L0 → ❨G2,L0❩ ⊢ ⬈ L2 → ❨G1,L1,T1❩ ≽ ❨G2,L2,T2❩.
/4 width=10 by fpb_intro, lpx_rpx, reqg_rpx_trans/ qed.

(* Inversion lemmas with extended rt-transition for full local envs *********)

lemma fpb_inv_req (G1) (G2) (L1) (L2) (T1) (T2):
      ❨G1,L1,T1❩ ≽ ❨G2,L2,T2❩ →
      ∃∃L0,L,T. ❨G1,L1,T1❩ ⬂⸮ ❨G2,L,T❩ & ❨G2,L❩ ⊢ T ⬈ T2 & L ≡[T] L0 & ❨G2,L0❩ ⊢ ⬈ L2.
#G1 #G2 #L1 #L2 #T1 #T2 * #L #T #H1 #HT2 #HL2
elim (rpx_inv_req_lpx … HL2) -HL2 #L0 #HL0 #HL02
/2 width=7 by ex4_3_intro/
qed-.

(* Forward lemmas with extended rt-transition for full local envs ***********)

lemma fpb_fwd_req (G1) (G2) (L1) (L2) (T1) (T2):
      ❨G1,L1,T1❩ ≽ ❨G2,L2,T2❩ →
      ∃∃L0,L,T. ❨G1,L1,T1❩ ⬂⸮ ❨G2,L,T❩ & ❨G2,L❩ ⊢ T ⬈ T2 & ❨G2,L❩ ⊢ ⬈ L0 & L0 ≡[T] L2.
#G1 #G2 #L1 #L2 #T1 #T2 * #L #T #H1 #HT2 #HL2
elim (rpx_fwd_lpx_req … HL2) -HL2 #L0 #HL0 #HL02
/2 width=7 by ex4_3_intro/
qed-.
