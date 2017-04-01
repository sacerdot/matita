include "basic_2/computation/cpxs_lift.ma".
include "basic_2/multiple/fqus_fqus.ma".

(* Advanced properties ******************************************************)

lemma lstas_cpxs: ∀h,o,G,L,T1,T2,d2. ⦃G, L⦄ ⊢ T1 •*[h, d2] T2 →
                  ∀d1. ⦃G, L⦄ ⊢ T1 ▪[h, o] d1 → d2 ≤ d1 → ⦃G, L⦄ ⊢ T1 ⬈*[h, o] T2.
#h #o #G #L #T1 #T2 #d2 #H elim H -G -L -T1 -T2 -d2 //
[ /3 width=3 by cpxs_sort, da_inv_sort/
| #G #L #K #V1 #V2 #W2 #i #d2 #HLK #_ #HVW2 #IHV12 #d1 #H #Hd21
  elim (da_inv_lref … H) -H * #K0 #V0 [| #d0 ] #HLK0
  lapply (drop_mono … HLK0 … HLK) -HLK0 #H destruct /3 width=7 by cpxs_delta/
| #G #L #K #V1 #V2 #W2 #i #d2 #HLK #_ #HVW2 #IHV12 #d1 #H #Hd21
  elim (da_inv_lref … H) -H * #K0 #V0 [| #d0 ] #HLK0
  lapply (drop_mono … HLK0 … HLK) -HLK0 #H destruct
  #HV1 #H destruct lapply (le_plus_to_le_c … Hd21) -Hd21
  /3 width=7 by cpxs_delta/
| /4 width=3 by cpxs_bind_dx, da_inv_bind/
| /4 width=3 by cpxs_flat_dx, da_inv_flat/
| /4 width=3 by cpxs_eps, da_inv_flat/
]
qed.

(* Properties on supclosure *************************************************)

lemma fqu_cpxs_trans: ∀h,o,G1,G2,L1,L2,T2,U2. ⦃G2, L2⦄ ⊢ T2 ⬈*[h, o] U2 →
                      ∀T1. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ →
                      ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ⬈*[h, o] U1 & ⦃G1, L1, U1⦄ ⊐ ⦃G2, L2, U2⦄.
#h #o #G1 #G2 #L1 #L2 #T2 #U2 #H @(cpxs_ind_dx … H) -T2 /2 width=3 by ex2_intro/
#T #T2 #HT2 #_ #IHTU2 #T1 #HT1 elim (fqu_cpx_trans … HT1 … HT2) -T
#T #HT1 #HT2 elim (IHTU2 … HT2) -T2 /3 width=3 by cpxs_strap2, ex2_intro/
qed-.

lemma fquq_cpxs_trans: ∀h,o,G1,G2,L1,L2,T2,U2. ⦃G2, L2⦄ ⊢ T2 ⬈*[h, o] U2 →
                       ∀T1. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄ →
                       ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ⬈*[h, o] U1 & ⦃G1, L1, U1⦄ ⊐⸮ ⦃G2, L2, U2⦄.
#h #o #G1 #G2 #L1 #L2 #T2 #U2 #HTU2 #T1 #H elim (fquq_inv_gen … H) -H
[ #HT12 elim (fqu_cpxs_trans … HTU2 … HT12) /3 width=3 by fqu_fquq, ex2_intro/
| * #H1 #H2 #H3 destruct /2 width=3 by ex2_intro/
]
qed-.

lemma fquq_lstas_trans: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄ →
                        ∀U2,d1. ⦃G2, L2⦄ ⊢ T2 •*[h, d1] U2 →
                        ∀d2. ⦃G2, L2⦄ ⊢ T2 ▪[h, o] d2 → d1 ≤ d2 →
                        ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ⬈*[h, o] U1 & ⦃G1, L1, U1⦄ ⊐⸮ ⦃G2, L2, U2⦄.
/3 width=5 by fquq_cpxs_trans, lstas_cpxs/ qed-.

lemma fqup_cpxs_trans: ∀h,o,G1,G2,L1,L2,T2,U2. ⦃G2, L2⦄ ⊢ T2 ⬈*[h, o] U2 →
                       ∀T1. ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄ →
                       ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ⬈*[h, o] U1 & ⦃G1, L1, U1⦄ ⊐+ ⦃G2, L2, U2⦄.
#h #o #G1 #G2 #L1 #L2 #T2 #U2 #H @(cpxs_ind_dx … H) -T2 /2 width=3 by ex2_intro/
#T #T2 #HT2 #_ #IHTU2 #T1 #HT1 elim (fqup_cpx_trans … HT1 … HT2) -T
#U1 #HTU1 #H2 elim (IHTU2 … H2) -T2 /3 width=3 by cpxs_strap2, ex2_intro/
qed-.

lemma fqus_cpxs_trans: ∀h,o,G1,G2,L1,L2,T2,U2. ⦃G2, L2⦄ ⊢ T2 ⬈*[h, o] U2 →
                       ∀T1. ⦃G1, L1, T1⦄ ⊐* ⦃G2, L2, T2⦄ →
                       ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ⬈*[h, o] U1 & ⦃G1, L1, U1⦄ ⊐* ⦃G2, L2, U2⦄.
#h #o #G1 #G2 #L1 #L2 #T2 #U2 #HTU2 #T1 #H elim (fqus_inv_gen … H) -H
[ #HT12 elim (fqup_cpxs_trans … HTU2 … HT12) /3 width=3 by fqup_fqus, ex2_intro/
| * #H1 #H2 #H3 destruct /2 width=3 by ex2_intro/
]
qed-.

lemma fqus_lstas_trans: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐* ⦃G2, L2, T2⦄ →
                        ∀U2,d1. ⦃G2, L2⦄ ⊢ T2 •*[h, d1] U2 →
                        ∀d2. ⦃G2, L2⦄ ⊢ T2 ▪[h, o] d2 → d1 ≤ d2 →
                        ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ⬈*[h, o] U1 & ⦃G1, L1, U1⦄ ⊐* ⦃G2, L2, U2⦄.
/3 width=6 by fqus_cpxs_trans, lstas_cpxs/ qed-.

(* Properties on supclosure *************************************************)

lemma fqu_cpxs_trans_neq: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ →
                          ∀U2. ⦃G2, L2⦄ ⊢ T2 ⬈*[h, o] U2 → (T2 = U2 → ⊥) →
                          ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ⬈*[h, o] U1 & T1 = U1 → ⊥ & ⦃G1, L1, U1⦄ ⊐ ⦃G2, L2, U2⦄.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
[ #I #G #L #V1 #V2 #HV12 #_ elim (lift_total V2 0 1)
  #U2 #HVU2 @(ex3_intro … U2)
  [1,3: /3 width=7 by fqu_drop, cpxs_delta, drop_pair, drop_drop/
  | #H destruct 
    lapply (lift_inv_lref2_be … HVU2 ? ?) -HVU2 //
  ]
| #I #G #L #V1 #T #V2 #HV12 #H @(ex3_intro … (②{I}V2.T))
  [1,3: /2 width=4 by fqu_pair_sn, cpxs_pair_sn/
  | #H0 destruct /2 width=1 by/
  ]
| #a #I #G #L #V #T1 #T2 #HT12 #H @(ex3_intro … (ⓑ{a,I}V.T2))
  [1,3: /2 width=4 by fqu_bind_dx, cpxs_bind/
  | #H0 destruct /2 width=1 by/
  ]
| #I #G #L #V #T1 #T2 #HT12 #H @(ex3_intro … (ⓕ{I}V.T2))
  [1,3: /2 width=4 by fqu_flat_dx, cpxs_flat/
  | #H0 destruct /2 width=1 by/
  ]
| #G #L #K #T1 #U1 #k #HLK #HTU1 #T2 #HT12 #H elim (lift_total T2 0 (k+1))
  #U2 #HTU2 @(ex3_intro … U2)
  [1,3: /2 width=10 by cpxs_lift, fqu_drop/
  | #H0 destruct /3 width=5 by lift_inj/
]
qed-.

lemma fquq_cpxs_trans_neq: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄ →
                           ∀U2. ⦃G2, L2⦄ ⊢ T2 ⬈*[h, o] U2 → (T2 = U2 → ⊥) →
                           ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ⬈*[h, o] U1 & T1 = U1 → ⊥ & ⦃G1, L1, U1⦄ ⊐⸮ ⦃G2, L2, U2⦄.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H12 #U2 #HTU2 #H elim (fquq_inv_gen … H12) -H12
[ #H12 elim (fqu_cpxs_trans_neq … H12 … HTU2 H) -T2
  /3 width=4 by fqu_fquq, ex3_intro/
| * #HG #HL #HT destruct /3 width=4 by ex3_intro/
]
qed-.

lemma fqup_cpxs_trans_neq: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄ →
                           ∀U2. ⦃G2, L2⦄ ⊢ T2 ⬈*[h, o] U2 → (T2 = U2 → ⊥) →
                           ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ⬈*[h, o] U1 & T1 = U1 → ⊥ & ⦃G1, L1, U1⦄ ⊐+ ⦃G2, L2, U2⦄.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H @(fqup_ind_dx … H) -G1 -L1 -T1
[ #G1 #L1 #T1 #H12 #U2 #HTU2 #H elim (fqu_cpxs_trans_neq … H12 … HTU2 H) -T2
  /3 width=4 by fqu_fqup, ex3_intro/
| #G #G1 #L #L1 #T #T1 #H1 #_ #IH12 #U2 #HTU2 #H elim (IH12 … HTU2 H) -T2
  #U1 #HTU1 #H #H12 elim (fqu_cpxs_trans_neq … H1 … HTU1 H) -T1
  /3 width=8 by fqup_strap2, ex3_intro/
]
qed-.

lemma fqus_cpxs_trans_neq: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐* ⦃G2, L2, T2⦄ →
                           ∀U2. ⦃G2, L2⦄ ⊢ T2 ⬈*[h, o] U2 → (T2 = U2 → ⊥) →
                           ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ⬈*[h, o] U1 & T1 = U1 → ⊥ & ⦃G1, L1, U1⦄ ⊐* ⦃G2, L2, U2⦄.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H12 #U2 #HTU2 #H elim (fqus_inv_gen … H12) -H12
[ #H12 elim (fqup_cpxs_trans_neq … H12 … HTU2 H) -T2
  /3 width=4 by fqup_fqus, ex3_intro/
| * #HG #HL #HT destruct /3 width=4 by ex3_intro/
]
qed-.
