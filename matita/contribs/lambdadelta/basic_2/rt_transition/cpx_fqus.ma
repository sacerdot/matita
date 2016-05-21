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

(* Properties on supclosure *************************************************)

lemma fqu_cpx_trans: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ →
                     ∀U2. ⦃G2, L2⦄ ⊢ T2 ➡[h, o] U2 →
                     ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡[h, o] U1 & ⦃G1, L1, U1⦄ ⊐ ⦃G2, L2, U2⦄.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2 
/3 width=3 by fqu_pair_sn, fqu_bind_dx, fqu_flat_dx, cpx_pair_sn, cpx_bind, cpx_flat, ex2_intro/
[ #I #G #L #V2 #U2 #HVU2
  elim (lift_total U2 0 1)
  /4 width=7 by fqu_drop, cpx_delta, drop_pair, drop_drop, ex2_intro/
| #G #L #K #T1 #U1 #k #HLK1 #HTU1 #T2 #HTU2
  elim (lift_total T2 0 (k+1))
  /3 width=11 by cpx_lift, fqu_drop, ex2_intro/
]
qed-.

lemma fquq_cpx_trans: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄ →
                      ∀U2. ⦃G2, L2⦄ ⊢ T2 ➡[h, o] U2 →
                      ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡[h, o] U1 & ⦃G1, L1, U1⦄ ⊐⸮ ⦃G2, L2, U2⦄.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H #U2 #HTU2 elim (fquq_inv_gen … H) -H
[ #HT12 elim (fqu_cpx_trans … HT12 … HTU2) /3 width=3 by fqu_fquq, ex2_intro/
| * #H1 #H2 #H3 destruct /2 width=3 by ex2_intro/
]
qed-.

lemma fqup_cpx_trans: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄ →
                      ∀U2. ⦃G2, L2⦄ ⊢ T2 ➡[h, o] U2 →
                      ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡[h, o] U1 & ⦃G1, L1, U1⦄ ⊐+ ⦃G2, L2, U2⦄.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H @(fqup_ind … H) -G2 -L2 -T2
[ #G2 #L2 #T2 #H12 #U2 #HTU2 elim (fqu_cpx_trans … H12 … HTU2) -T2
  /3 width=3 by fqu_fqup, ex2_intro/
| #G #G2 #L #L2 #T #T2 #_ #HT2 #IHT1 #U2 #HTU2
  elim (fqu_cpx_trans … HT2 … HTU2) -T2 #T2 #HT2 #HTU2
  elim (IHT1 … HT2) -T /3 width=7 by fqup_strap1, ex2_intro/
]
qed-.

lemma fqus_cpx_trans: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐* ⦃G2, L2, T2⦄ →
                      ∀U2. ⦃G2, L2⦄ ⊢ T2 ➡[h, o] U2 →
                      ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡[h, o] U1 & ⦃G1, L1, U1⦄ ⊐* ⦃G2, L2, U2⦄.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H #U2 #HTU2 elim (fqus_inv_gen … H) -H
[ #HT12 elim (fqup_cpx_trans … HT12 … HTU2) /3 width=3 by fqup_fqus, ex2_intro/
| * #H1 #H2 #H3 destruct /2 width=3 by ex2_intro/
]
qed-.

lemma fqu_cpx_trans_neq: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ →
                         ∀U2. ⦃G2, L2⦄ ⊢ T2 ➡[h, o] U2 → (T2 = U2 → ⊥) →
                         ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡[h, o] U1 & T1 = U1 → ⊥ & ⦃G1, L1, U1⦄ ⊐ ⦃G2, L2, U2⦄.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
[ #I #G #L #V1 #V2 #HV12 #_ elim (lift_total V2 0 1)
  #U2 #HVU2 @(ex3_intro … U2)
  [1,3: /3 width=7 by fqu_drop, cpx_delta, drop_pair, drop_drop/
  | #H destruct
    lapply (lift_inv_lref2_be … HVU2 ? ?) -HVU2 //
  ]
| #I #G #L #V1 #T #V2 #HV12 #H @(ex3_intro … (②{I}V2.T))
  [1,3: /2 width=4 by fqu_pair_sn, cpx_pair_sn/
  | #H0 destruct /2 width=1 by/
  ]
| #a #I #G #L #V #T1 #T2 #HT12 #H @(ex3_intro … (ⓑ{a,I}V.T2))
  [1,3: /2 width=4 by fqu_bind_dx, cpx_bind/
  | #H0 destruct /2 width=1 by/
  ]
| #I #G #L #V #T1 #T2 #HT12 #H @(ex3_intro … (ⓕ{I}V.T2))
  [1,3: /2 width=4 by fqu_flat_dx, cpx_flat/
  | #H0 destruct /2 width=1 by/
  ]
| #G #L #K #T1 #U1 #k #HLK #HTU1 #T2 #HT12 #H elim (lift_total T2 0 (k+1))
  #U2 #HTU2 @(ex3_intro … U2)
  [1,3: /2 width=10 by cpx_lift, fqu_drop/
  | #H0 destruct /3 width=5 by lift_inj/
]
qed-.

lemma fquq_cpx_trans_neq: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄ →
                          ∀U2. ⦃G2, L2⦄ ⊢ T2 ➡[h, o] U2 → (T2 = U2 → ⊥) →
                          ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡[h, o] U1 & T1 = U1 → ⊥ & ⦃G1, L1, U1⦄ ⊐⸮ ⦃G2, L2, U2⦄.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H12 #U2 #HTU2 #H elim (fquq_inv_gen … H12) -H12
[ #H12 elim (fqu_cpx_trans_neq … H12 … HTU2 H) -T2
  /3 width=4 by fqu_fquq, ex3_intro/
| * #HG #HL #HT destruct /3 width=4 by ex3_intro/
]
qed-.

lemma fqup_cpx_trans_neq: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄ →
                          ∀U2. ⦃G2, L2⦄ ⊢ T2 ➡[h, o] U2 → (T2 = U2 → ⊥) →
                          ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡[h, o] U1 & T1 = U1 → ⊥ & ⦃G1, L1, U1⦄ ⊐+ ⦃G2, L2, U2⦄.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H @(fqup_ind_dx … H) -G1 -L1 -T1
[ #G1 #L1 #T1 #H12 #U2 #HTU2 #H elim (fqu_cpx_trans_neq … H12 … HTU2 H) -T2
  /3 width=4 by fqu_fqup, ex3_intro/
| #G #G1 #L #L1 #T #T1 #H1 #_ #IH12 #U2 #HTU2 #H elim (IH12 … HTU2 H) -T2
  #U1 #HTU1 #H #H12 elim (fqu_cpx_trans_neq … H1 … HTU1 H) -T1
  /3 width=8 by fqup_strap2, ex3_intro/
]
qed-.

lemma fqus_cpx_trans_neq: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐* ⦃G2, L2, T2⦄ →
                          ∀U2. ⦃G2, L2⦄ ⊢ T2 ➡[h, o] U2 → (T2 = U2 → ⊥) →
                          ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡[h, o] U1 & T1 = U1 → ⊥ & ⦃G1, L1, U1⦄ ⊐* ⦃G2, L2, U2⦄.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H12 #U2 #HTU2 #H elim (fqus_inv_gen … H12) -H12
[ #H12 elim (fqup_cpx_trans_neq … H12 … HTU2 H) -T2
  /3 width=4 by fqup_fqus, ex3_intro/
| * #HG #HL #HT destruct /3 width=4 by ex3_intro/
]
qed-.
