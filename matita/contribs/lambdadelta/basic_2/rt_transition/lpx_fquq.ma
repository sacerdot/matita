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

include "static_2/s_transition/fquq.ma".
include "basic_2/rt_transition/lpx.ma".

(* UNBOUND PARALLEL RT-TRANSITION FOR FULL LOCAL ENVIRONMENTS ***************)

(* Properties with extended structural successor for closures ***************)

lemma lpx_fqu_trans (h) (b): ∀G1,G2,L1,L2,T1,T2. ⦃G1,L1,T1⦄ ⬂[b] ⦃G2,L2,T2⦄ →
                             ∀K1. ⦃G1,K1⦄ ⊢ ⬈[h] L1 →
                             ∃∃K2,T. ⦃G1,K1⦄ ⊢ T1 ⬈[h] T & ⦃G1,K1,T⦄ ⬂[b] ⦃G2,K2,T2⦄ & ⦃G2,K2⦄ ⊢ ⬈[h] L2.
#h #b #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
[ #I #G #K #V #K1 #H
  elim (lpx_inv_pair_dx … H) -H #K0 #V0 #HK0 #HV0 #H destruct
  elim (lifts_total V (𝐔❴1❵)) #T #HVT
  /3 width=5 by cpx_delta, fqu_drop, ex3_2_intro/
| /3 width=5 by cpx_pair_sn, fqu_pair_sn, ex3_2_intro/
| /3 width=5 by lpx_bind_refl_dx, cpx_pair_sn, fqu_bind_dx, ex3_2_intro/
| /3 width=5 by lpx_bind_refl_dx, cpx_pair_sn, fqu_clear, ex3_2_intro/
| /3 width=5 by cpx_pair_sn, fqu_flat_dx, ex3_2_intro/
| #I #G #K #T #U #HTU #K1 #H
  elim (lpx_inv_bind_dx … H) -H #I0 #K0 #HK0 #HI0 #H destruct
  /3 width=5 by fqu_drop, ex3_2_intro/
]
qed-.

lemma fqu_lpx_trans (h) (b): ∀G1,G2,L1,L2,T1,T2. ⦃G1,L1,T1⦄ ⬂[b] ⦃G2,L2,T2⦄ →
                             ∀K2. ⦃G2,L2⦄ ⊢ ⬈[h] K2 →
                             ∃∃K1,T. ⦃G1,L1⦄ ⊢ ⬈[h] K1 & ⦃G1,L1⦄ ⊢ T1 ⬈[h] T & ⦃G1,K1,T⦄ ⬂[b] ⦃G2,K2,T2⦄.
#h #b #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
[ /3 width=5 by lpx_bind_refl_dx, fqu_lref_O, ex3_2_intro/
| /3 width=5 by cpx_pair_sn, fqu_pair_sn, ex3_2_intro/
| #p #I #G2 #L2 #V2 #T2 #Hb #X #H
  elim (lpx_inv_pair_sn … H) -H #K2 #W2 #HLK2 #HVW2 #H destruct
  /3 width=5 by cpx_pair_sn, fqu_bind_dx, ex3_2_intro/
| #p #I #G2 #L2 #V2 #T2 #Hb #X #H
  elim (lpx_inv_unit_sn … H) -H #K2 #HLK2 #H destruct
  /3 width=5 by cpx_pair_sn, fqu_clear, ex3_2_intro/
| /3 width=5 by cpx_pair_sn, fqu_flat_dx, ex3_2_intro/
| /3 width=5 by lpx_bind_refl_dx, fqu_drop, ex3_2_intro/
]
qed-.

(* Properties with extended optional structural successor for closures ******)

lemma lpx_fquq_trans (h) (b): ∀G1,G2,L1,L2,T1,T2. ⦃G1,L1,T1⦄ ⬂⸮[b] ⦃G2,L2,T2⦄ →
                              ∀K1. ⦃G1,K1⦄ ⊢ ⬈[h] L1 →
                              ∃∃K2,T. ⦃G1,K1⦄ ⊢ T1 ⬈[h] T & ⦃G1,K1,T⦄ ⬂⸮[b] ⦃G2,K2,T2⦄ & ⦃G2,K2⦄ ⊢ ⬈[h] L2.
#h #b #G1 #G2 #L1 #L2 #T1 #T2 #H #K1 #HKL1 cases H -H
[ #H12 elim (lpx_fqu_trans … H12 … HKL1) -L1 /3 width=5 by fqu_fquq, ex3_2_intro/
| * #H1 #H2 #H3 destruct /2 width=5 by ex3_2_intro/
]
qed-.

lemma fquq_lpx_trans (h) (b): ∀G1,G2,L1,L2,T1,T2. ⦃G1,L1,T1⦄ ⬂⸮[b] ⦃G2,L2,T2⦄ →
                              ∀K2. ⦃G2,L2⦄ ⊢ ⬈[h] K2 →
                              ∃∃K1,T. ⦃G1,L1⦄ ⊢ ⬈[h] K1 & ⦃G1,L1⦄ ⊢ T1 ⬈[h] T & ⦃G1,K1,T⦄ ⬂⸮[b] ⦃G2,K2,T2⦄.
#h #b #G1 #G2 #L1 #L2 #T1 #T2 #H #K2 #HLK2 cases H -H
[ #H12 elim (fqu_lpx_trans … H12 … HLK2) /3 width=5 by fqu_fquq, ex3_2_intro/
| * #H1 #H2 #H3 destruct /2 width=5 by ex3_2_intro/
]
qed-.
