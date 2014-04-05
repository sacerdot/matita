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

include "basic_2/reduction/cpx_llpx_sn.ma".
include "basic_2/reduction/cpx_lift.ma".
include "basic_2/reduction/llpx.ma".

(* LAZY SN EXTENDED PARALLEL REDUCTION FOR LOCAL ENVIRONMENTS ***************)

(* Advanced inversion lemmas ************************************************)

lemma llpx_inv_lref_ge_dx: ∀h,g,G,L1,L2,d,i. ⦃G, L1⦄ ⊢ ➡[h, g, #i, d] L2 → d ≤ i →
                           ∀I,K2,V2. ⇩[i] L2 ≡ K2.ⓑ{I}V2 →
                           ∃∃K1,V1. ⇩[i] L1 ≡ K1.ⓑ{I}V1 &
                                    ⦃G, K1⦄ ⊢ ➡[h, g, V1, 0] K2 & ⦃G, K1⦄ ⊢ V1 ➡[h, g] V2.
/2 width=5 by llpx_sn_inv_lref_ge_dx/ qed-.

lemma llpx_inv_lref_ge_sn: ∀h,g,G,L1,L2,d,i. ⦃G, L1⦄ ⊢ ➡[h, g, #i, d] L2 → d ≤ i →
                           ∀I,K1,V1. ⇩[i] L1 ≡ K1.ⓑ{I}V1 →
                           ∃∃K2,V2. ⇩[i] L2 ≡ K2.ⓑ{I}V2 &
                                    ⦃G, K1⦄ ⊢ ➡[h, g, V1, 0] K2 & ⦃G, K1⦄ ⊢ V1 ➡[h, g] V2.
/2 width=5 by llpx_sn_inv_lref_ge_sn/ qed-.

lemma llpx_inv_lref_ge_bi: ∀h,g,G,L1,L2,d,i. ⦃G, L1⦄ ⊢ ➡[h, g, #i, d] L2 → d ≤ i →
                           ∀I1,I2,K1,K2,V1,V2.
                           ⇩[i] L1 ≡ K1.ⓑ{I1}V1 → ⇩[i] L2 ≡ K2.ⓑ{I2}V2 →
                           ∧∧ I1 = I2 & ⦃G, K1⦄ ⊢ ➡[h, g, V1, 0] K2 & ⦃G, K1⦄ ⊢ V1 ➡[h, g] V2.
/2 width=8 by llpx_sn_inv_lref_ge_bi/ qed-.

lemma llpx_inv_bind_O: ∀h,g,a,I,G,L1,L2,V,T. ⦃G, L1⦄ ⊢ ➡ [h, g, ⓑ{a,I}V.T, 0] L2 →
                       ⦃G, L1⦄ ⊢ ➡[h, g, V, 0] L2 ∧ ⦃G, L1.ⓑ{I}V⦄ ⊢ ➡[h, g, T, 0] L2.ⓑ{I}V.
/2 width=2 by llpx_sn_inv_bind_O/ qed-.

lemma llpx_bind_repl_O: ∀h,g,I,G,L1,L2,V1,V2,T. ⦃G, L1.ⓑ{I}V1⦄ ⊢ ➡[h, g, T, 0] L2.ⓑ{I}V2 →
                        ∀J,W1,W2. ⦃G, L1⦄ ⊢ ➡[h, g, W1, 0] L2 → ⦃G, L1⦄ ⊢ W1 ➡[h, g] W2 → ⦃G, L1.ⓑ{J}W1⦄ ⊢ ➡[h, g, T, 0] L2.ⓑ{J}W2.
/2 width=4 by llpx_sn_bind_repl_O/ qed-.

(* Advanced forward lemmas **************************************************)

lemma llpx_fwd_bind_O_dx: ∀h,g,a,I,G,L1,L2,V,T. ⦃G, L1⦄ ⊢ ➡[h, g, ⓑ{a,I}V.T, 0] L2 →
                          ⦃G, L1.ⓑ{I}V⦄ ⊢ ➡[h, g, T, 0] L2.ⓑ{I}V.
/2 width=3 by llpx_sn_fwd_bind_O_dx/ qed-.

(* Advanced properties ******************************************************)

lemma llpx_cpx_conf: ∀h,g,G. s_r_confluent1 … (cpx h g G) (llpx h g G 0).
/3 width=10 by cpx_llpx_sn_conf, cpx_inv_lift1, cpx_lift/ qed-.

(* Inversion lemmas on relocation *******************************************)

lemma llpx_ldrop_trans_O: ∀h,g,G,L1,L2,U. ⦃G, L1⦄ ⊢ ➡[h, g, U, 0] L2 →
                          ∀K2,e. ⇩[e] L2 ≡ K2 → ∀T. ⇧[0, e] T ≡ U →
                          ∃∃K1. ⇩[e] L1 ≡ K1 & ⦃G, K1⦄ ⊢ ➡[h, g, T, 0] K2.
/2 width=5 by llpx_sn_ldrop_trans_O/ qed-.

(* Properties on supclosure *************************************************)

lemma llpx_fqu_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃ ⦃G2, L2, T2⦄ →
                      ∀K1. ⦃G1, K1⦄ ⊢ ➡[h, g, T1, 0] L1 →
                      ∃∃K2,T. ⦃G1, K1⦄ ⊢ T1 ➡[h, g] T & ⦃G1, K1, T⦄ ⊃ ⦃G2, K2, T2⦄ & ⦃G2, K2⦄ ⊢ ➡[h, g, T2, 0] L2.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
/3 width=7 by llpx_fwd_bind_O_dx, llpx_fwd_pair_sn,llpx_fwd_flat_dx, ex3_2_intro/
[ #I #G1 #L1 #V1 #K1 #H elim (llpx_inv_lref_ge_dx … H) -H [5,6: // |2,3,4: skip ]
  #Y1 #W1 #HKL1 #HW1 #HWV1 elim (lift_total V1 0 1)
  /4 width=7 by llpx_cpx_conf, cpx_delta, fqu_drop, ldrop_fwd_drop2, ex3_2_intro/
| #G #L1 #K1 #T1 #U1 #e #HLK1 #HTU1 #L0 #HU1
  elim (llpx_ldrop_trans_O … HU1 … HLK1) -L1
  /3 width=5 by fqu_drop, ex3_2_intro/
]
qed-.

lemma llpx_fquq_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃⸮ ⦃G2, L2, T2⦄ →
                       ∀K1. ⦃G1, K1⦄ ⊢ ➡[h, g, T1, 0] L1 →
                       ∃∃K2,T. ⦃G1, K1⦄ ⊢ T1 ➡[h, g] T & ⦃G1, K1, T⦄ ⊃⸮ ⦃G2, K2, T2⦄ & ⦃G2, K2⦄ ⊢ ➡[h, g, T2, 0] L2.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H #K1 #HKL1 elim (fquq_inv_gen … H) -H
[ #HT12 elim (llpx_fqu_trans … HT12 … HKL1) /3 width=5 by fqu_fquq, ex3_2_intro/
| * #H1 #H2 #H3 destruct /2 width=5 by ex3_2_intro/
]
qed-.
