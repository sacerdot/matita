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

include "basic_2/rt_transition/lpx_reqg.ma".
include "basic_2/rt_transition/fpbc.ma".

(* PROPER PARALLEL RST-TRANSITION FOR CLOSURES ******************************)

(* Properties with extended rt-transition for full local envs ***************)

(* Basic_2A1: uses: fpb_lpx *)
lemma lpx_fpbc (G) (T):
      ∀L1,L2. ❪G,L1❫ ⊢ ⬈ L2 → (L1 ≅[T] L2 → ⊥) → ❪G,L1,T❫ ≻ ❪G,L2,T❫.
/3 width=1 by rpx_fpbc, lpx_rpx/ qed.

(* Forward lemmas with extended rt-transition for full local envs ***********)

lemma fpbc_fwd_lpx (G1) (G2) (L1) (L2) (T1) (T2):
      ❪G1,L1,T1❫ ≻ ❪G2,L2,T2❫ →
      ∨∨ ∃∃G,L,T. ❪G1,L1,T1❫ ⬂ ❪G,L,T❫ & ❪G,L,T❫ ≽ ❪G2,L2,T2❫
       | ∃∃T. ❪G1,L1❫ ⊢ T1 ⬈ T & T1 ≅ T → ⊥ & ❪G1,L1,T❫ ≽ ❪G2,L2,T2❫
       | ∃∃L. ❪G1,L1❫ ⊢ ⬈ L & (L1 ≅[T1] L → ⊥) & ❪G1,L,T1❫ ≽ ❪G2,L2,T2❫.
#G1 #G2 #L1 #L2 #T1 #T2 #H
elim (fpbc_inv_gen sfull … H) -H #H12 #Hn12
elim (fpb_inv_gen … H12) -H12 #L #T #H1 #HT2 #HL2
elim H1 -H1 [ /4 width=9 by fpb_intro, ex2_3_intro, or3_intro0/ ]
* #H1 #H2 #H3 destruct
elim (teqg_dec sfull … T T2)
[ -HT2 #HT2 |*: /5 width=11 by fpb_intro, cpx_rex_conf_sn, ex3_intro, or3_intro1, sfull_dec/ ]
elim (rpx_fwd_lpx_reqg sfull … HL2) -HL2 // #L0 #HL0 #HL02
elim (reqg_dec sfull … L L0 T)
[ -HL0 #HL0 |*: /5 width=11 by fpb_intro, reqg_rpx, teqg_cpx, ex3_intro, or3_intro2, sfull_dec/ ]
elim Hn12 -Hn12 /3 width=3 by feqg_intro_sn, reqg_trans/
qed-.
