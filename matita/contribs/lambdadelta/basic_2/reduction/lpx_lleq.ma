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

include "basic_2/multiple/llor_drop.ma".
include "basic_2/multiple/llpx_sn_llor.ma".
include "basic_2/multiple/llpx_sn_lpx_sn.ma".
include "basic_2/multiple/lleq_leq.ma".
include "basic_2/multiple/lleq_llor.ma".
include "basic_2/reduction/cpx_leq.ma".
include "basic_2/reduction/cpx_lleq.ma".
include "basic_2/reduction/lpx_frees.ma".

(* SN EXTENDED PARALLEL REDUCTION FOR LOCAL ENVIRONMENTS ********************)

(* Properties on lazy equivalence for local environments ********************)

(* Note: contains a proof of llpx_cpx_conf *)
lemma lleq_lpx_trans: ∀h,g,G,L2,K2. ⦃G, L2⦄ ⊢ ➡[h, g] K2 →
                      ∀L1,T,d. L1 ≡[T, d] L2 →
                      ∃∃K1. ⦃G, L1⦄ ⊢ ➡[h, g] K1 & K1 ≡[T, d] K2.
#h #g #G #L2 #K2 #HLK2 #L1 #T #d #HL12
lapply (lpx_fwd_length … HLK2) #H1
lapply (lleq_fwd_length … HL12) #H2
lapply (lpx_sn_llpx_sn … T … d HLK2) // -HLK2 #H
lapply (lleq_llpx_sn_trans … HL12 … H) /2 width=3 by lleq_cpx_trans/ -HL12 -H #H
elim (llor_total L1 K2 T d) // -H1 -H2 #K1 #HLK1
lapply (llpx_sn_llor_dx_sym … H … HLK1)
[ /2 width=6 by cpx_frees_trans/
| /3 width=10 by cpx_llpx_sn_conf, cpx_inv_lift1, cpx_lift/
| /3 width=5 by llpx_sn_llor_fwd_sn, ex2_intro/
]
qed-.

lemma lpx_lleq_fqu_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ →
                          ∀K1. ⦃G1, K1⦄ ⊢ ➡[h, g] L1 → K1 ≡[T1, 0] L1 →
                          ∃∃K2. ⦃G1, K1, T1⦄ ⊐ ⦃G2, K2, T2⦄ & ⦃G2, K2⦄ ⊢ ➡[h, g] L2 & K2 ≡[T2, 0] L2.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
[ #I #G1 #L1 #V1 #X #H1 #H2 elim (lpx_inv_pair2 … H1) -H1
  #K0 #V0 #H1KL1 #_ #H destruct
  elim (lleq_inv_lref_ge_dx … H2 ? I L1 V1) -H2 //
  #K1 #H #H2KL1 lapply (drop_inv_O2 … H) -H #H destruct
  /2 width=4 by fqu_lref_O, ex3_intro/
| * [ #a ] #I #G1 #L1 #V1 #T1 #K1 #HLK1 #H
  [ elim (lleq_inv_bind … H)
  | elim (lleq_inv_flat … H)
  ] -H /2 width=4 by fqu_pair_sn, ex3_intro/
| #a #I #G1 #L1 #V1 #T1 #K1 #HLK1 #H elim (lleq_inv_bind_O … H) -H
  /3 width=4 by lpx_pair, fqu_bind_dx, ex3_intro/
| #I #G1 #L1 #V1 #T1 #K1 #HLK1 #H elim (lleq_inv_flat … H) -H
  /2 width=4 by fqu_flat_dx, ex3_intro/
| #G1 #L1 #L #T1 #U1 #e #HL1 #HTU1 #K1 #H1KL1 #H2KL1
  elim (drop_O1_le (Ⓕ) (e+1) K1)
  [ #K #HK1 lapply (lleq_inv_lift_le … H2KL1 … HK1 HL1 … HTU1 ?) -H2KL1 //
    #H2KL elim (lpx_drop_trans_O1 … H1KL1 … HL1) -L1
    #K0 #HK10 #H1KL lapply (drop_mono … HK10 … HK1) -HK10 #H destruct
    /3 width=4 by fqu_drop, ex3_intro/
  | lapply (drop_fwd_length_le2 … HL1) -L -T1 -g
    lapply (lleq_fwd_length … H2KL1) //
  ]
]
qed-.

lemma lpx_lleq_fquq_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄ →
                           ∀K1. ⦃G1, K1⦄ ⊢ ➡[h, g] L1 → K1 ≡[T1, 0] L1 →
                           ∃∃K2. ⦃G1, K1, T1⦄ ⊐⸮ ⦃G2, K2, T2⦄ & ⦃G2, K2⦄ ⊢ ➡[h, g] L2 & K2 ≡[T2, 0] L2.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H #K1 #H1KL1 #H2KL1
elim (fquq_inv_gen … H) -H
[ #H elim (lpx_lleq_fqu_trans … H … H1KL1 H2KL1) -L1
  /3 width=4 by fqu_fquq, ex3_intro/
| * #HG #HL #HT destruct /2 width=4 by ex3_intro/
]
qed-.

lemma lpx_lleq_fqup_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄ →
                           ∀K1. ⦃G1, K1⦄ ⊢ ➡[h, g] L1 → K1 ≡[T1, 0] L1 →
                           ∃∃K2. ⦃G1, K1, T1⦄ ⊐+ ⦃G2, K2, T2⦄ & ⦃G2, K2⦄ ⊢ ➡[h, g] L2 & K2 ≡[T2, 0] L2.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H @(fqup_ind … H) -G2 -L2 -T2
[ #G2 #L2 #T2 #H #K1 #H1KL1 #H2KL1 elim (lpx_lleq_fqu_trans … H … H1KL1 H2KL1) -L1
  /3 width=4 by fqu_fqup, ex3_intro/
| #G #G2 #L #L2 #T #T2 #_ #HT2 #IHT1 #K1 #H1KL1 #H2KL1 elim (IHT1 … H2KL1) // -L1
  #K #HT1 #H1KL #H2KL elim (lpx_lleq_fqu_trans … HT2 … H1KL H2KL) -L
  /3 width=5 by fqup_strap1, ex3_intro/
]
qed-.

lemma lpx_lleq_fqus_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐* ⦃G2, L2, T2⦄ →
                           ∀K1. ⦃G1, K1⦄ ⊢ ➡[h, g] L1 → K1 ≡[T1, 0] L1 →
                           ∃∃K2. ⦃G1, K1, T1⦄ ⊐* ⦃G2, K2, T2⦄ & ⦃G2, K2⦄ ⊢ ➡[h, g] L2 & K2 ≡[T2, 0] L2.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H #K1 #H1KL1 #H2KL1
elim (fqus_inv_gen … H) -H
[ #H elim (lpx_lleq_fqup_trans … H … H1KL1 H2KL1) -L1
  /3 width=4 by fqup_fqus, ex3_intro/
| * #HG #HL #HT destruct /2 width=4 by ex3_intro/
]
qed-.

fact leq_lpx_trans_lleq_aux: ∀h,g,G,L1,L0,d,e. L1 ⩬[d, e] L0 → e = ∞ →
                             ∀L2. ⦃G, L0⦄ ⊢ ➡[h, g] L2 →
                             ∃∃L. L ⩬[d, e] L2 & ⦃G, L1⦄ ⊢ ➡[h, g] L &
                                  (∀T. L0 ≡[T, d] L2 ↔ L1 ≡[T, d] L).
#h #g #G #L1 #L0 #d #e #H elim H -L1 -L0 -d -e
[ #d #e #_ #L2 #H >(lpx_inv_atom1 … H) -H
  /3 width=5 by ex3_intro, conj/
| #I1 #I0 #L1 #L0 #V1 #V0 #_ #_ #He destruct
| #I #L1 #L0 #V1 #e #HL10 #IHL10 #He #Y #H
  elim (lpx_inv_pair1 … H) -H #L2 #V2 #HL02 #HV02 #H destruct
  lapply (ysucc_inv_Y_dx … He) -He #He
  elim (IHL10 … HL02) // -IHL10 -HL02 #L #HL2 #HL1 #IH
  @(ex3_intro … (L.ⓑ{I}V2)) /3 width=3 by lpx_pair, leq_cpx_trans, leq_pair/
  #T elim (IH T) #HL0dx #HL0sn
  @conj #H @(lleq_leq_repl … H) -H /3 width=1 by leq_sym, leq_pair_O_Y/
| #I1 #I0 #L1 #L0 #V1 #V0 #d #e #HL10 #IHL10 #He #Y #H
  elim (lpx_inv_pair1 … H) -H #L2 #V2 #HL02 #HV02 #H destruct
  elim (IHL10 … HL02) // -IHL10 -HL02 #L #HL2 #HL1 #IH
  @(ex3_intro … (L.ⓑ{I1}V1)) /3 width=1 by lpx_pair, leq_succ/
  #T elim (IH T) #HL0dx #HL0sn
  @conj #H @(lleq_leq_repl … H) -H /3 width=1 by leq_sym, leq_succ/
]
qed-.

lemma leq_lpx_trans_lleq: ∀h,g,G,L1,L0,d. L1 ⩬[d, ∞] L0 →
                          ∀L2. ⦃G, L0⦄ ⊢ ➡[h, g] L2 →
                          ∃∃L. L ⩬[d, ∞] L2 & ⦃G, L1⦄ ⊢ ➡[h, g] L &
                               (∀T. L0 ≡[T, d] L2 ↔ L1 ≡[T, d] L).
/2 width=1 by leq_lpx_trans_lleq_aux/ qed-.
