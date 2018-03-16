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

include "basic_2/rt_transition/lfpx_drops.ma".
include "basic_2/rt_transition/lfpx_fsle.ma".
include "basic_2/s_transition/fquq.ma".

(* UNCOUNTED PARALLEL RT-TRANSITION FOR LOCAL ENV.S ON REFERRED ENTRIES *****)

(* Properties with extended structural successor for closures ***************)

(* Basic_2A1: uses: lpx_fqu_trans *)
lemma lfpx_fqu_trans: ∀h,b,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐[b] ⦃G2, L2, T2⦄ →
                      ∀K1. ⦃G1, K1⦄ ⊢ ⬈[h, T1] L1 →
                      ∃∃K2,T. ⦃G1, K1⦄ ⊢ T1 ⬈[h] T & ⦃G1, K1, T⦄ ⊐[b] ⦃G2, K2, T2⦄ & ⦃G2, K2⦄ ⊢ ⬈[h, T2] L2.
#h #b #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
[ #I #G #K #V #K1 #H
  elim (lfpx_inv_zero_pair_dx … H) -H #K0 #V0 #HK0 #HV0 #H destruct
  elim (lifts_total V (𝐔❴1❵)) #T #HVT
  /3 width=7 by lfpx_cpx_conf, cpx_delta, fqu_drop, ex3_2_intro/
| /3 width=7 by lfpx_fwd_pair_sn, cpx_pair_sn, fqu_pair_sn, ex3_2_intro/
| /3 width=6 by lfpx_fwd_bind_dx, cpx_pair_sn, fqu_bind_dx, ex3_2_intro/
| /3 width=8 by lfpx_fwd_bind_dx_void, cpx_pair_sn, fqu_clear, ex3_2_intro/
| /3 width=7 by lfpx_fwd_flat_dx, cpx_pair_sn, fqu_flat_dx, ex3_2_intro/
| #I #G #K #T #U #HTU #K1 #H
  elim (lfpx_drops_trans … H (Ⓣ) … HTU) -H
  [|*: /3 width=2 by drops_refl, drops_drop/ ] -I #K0 #HK10 #HK0
  elim (drops_inv_succ … HK10) -HK10 #I #Y #HY #H destruct
  lapply (drops_fwd_isid … HY ?) -HY // #H destruct
  /3 width=5 by fqu_drop, ex3_2_intro/
]
qed-.

(* Properties with extended optional structural successor for closures ******)

(* Basic_2A1: uses: lpx_fquq_trans *)
lemma lfpx_fquq_trans: ∀h,b,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⸮[b] ⦃G2, L2, T2⦄ →
                       ∀K1. ⦃G1, K1⦄ ⊢ ⬈[h, T1] L1 →
                       ∃∃K2,T. ⦃G1, K1⦄ ⊢ T1 ⬈[h] T & ⦃G1, K1, T⦄ ⊐⸮[b] ⦃G2, K2, T2⦄ & ⦃G2, K2⦄ ⊢ ⬈[h, T2] L2.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H #K1 #HKL1 cases H -H
[ #H12 elim (lfpx_fqu_trans … H12 … HKL1) -L1 /3 width=5 by fqu_fquq, ex3_2_intro/
| * #H1 #H2 #H3 destruct /2 width=5 by ex3_2_intro/
]
qed-.
