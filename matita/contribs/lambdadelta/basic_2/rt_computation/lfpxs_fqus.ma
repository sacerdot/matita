(* Properties on supclosure *************************************************)

lemma lpx_fqup_trans: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄ →
                      ∀K1. ⦃G1, K1⦄ ⊢ ➡[h, o] L1 →
                      ∃∃K2,T. ⦃G1, K1⦄ ⊢ T1 ➡*[h, o] T & ⦃G1, K1, T⦄ ⊐+ ⦃G2, K2, T2⦄ & ⦃G2, K2⦄ ⊢ ➡[h, o] L2.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H @(fqup_ind … H) -G2 -L2 -T2
[ #G2 #L2 #T2 #H12 #K1 #HKL1 elim (lpx_fqu_trans … H12 … HKL1) -L1
  /3 width=5 by cpx_cpxs, fqu_fqup, ex3_2_intro/
| #G #G2 #L #L2 #T #T2 #_ #H2 #IH1 #K1 #HLK1 elim (IH1 … HLK1) -L1
  #L0 #T0 #HT10 #HT0 #HL0 elim (lpx_fqu_trans … H2 … HL0) -L
  #L #T3 #HT3 #HT32 #HL2 elim (fqup_cpx_trans … HT0 … HT3) -T
  /3 width=7 by cpxs_strap1, fqup_strap1, ex3_2_intro/
]
qed-.

lemma lpx_fqus_trans: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐* ⦃G2, L2, T2⦄ →
                      ∀K1. ⦃G1, K1⦄ ⊢ ➡[h, o] L1 →
                      ∃∃K2,T. ⦃G1, K1⦄ ⊢ T1 ➡*[h, o] T & ⦃G1, K1, T⦄ ⊐* ⦃G2, K2, T2⦄ & ⦃G2, K2⦄ ⊢ ➡[h, o] L2.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H @(fqus_ind … H) -G2 -L2 -T2 [ /2 width=5 by ex3_2_intro/ ]
#G #G2 #L #L2 #T #T2 #_ #H2 #IH1 #K1 #HLK1 elim (IH1 … HLK1) -L1
#L0 #T0 #HT10 #HT0 #HL0 elim (lpx_fquq_trans … H2 … HL0) -L
#L #T3 #HT3 #HT32 #HL2 elim (fqus_cpx_trans … HT0 … HT3) -T
/3 width=7 by cpxs_strap1, fqus_strap1, ex3_2_intro/
qed-.

lemma lpxs_fquq_trans: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄ →
                       ∀K1. ⦃G1, K1⦄ ⊢ ➡*[h, o] L1 →
                       ∃∃K2,T. ⦃G1, K1⦄ ⊢ T1 ➡*[h, o] T & ⦃G1, K1, T⦄ ⊐⸮ ⦃G2, K2, T2⦄ & ⦃G2, K2⦄ ⊢ ➡*[h, o] L2.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #HT12 #K1 #H @(lpxs_ind_dx … H) -K1
[ /2 width=5 by ex3_2_intro/
| #K1 #K #HK1 #_ * #L #T #HT1 #HT2 #HL2 -HT12
  lapply (lpx_cpxs_trans … HT1 … HK1) -HT1
  elim (lpx_fquq_trans … HT2 … HK1) -K
  /3 width=7 by lpxs_strap2, cpxs_strap1, ex3_2_intro/
]
qed-.

lemma lpxs_fqup_trans: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄ →
                       ∀K1. ⦃G1, K1⦄ ⊢ ➡*[h, o] L1 →
                       ∃∃K2,T. ⦃G1, K1⦄ ⊢ T1 ➡*[h, o] T & ⦃G1, K1, T⦄ ⊐+ ⦃G2, K2, T2⦄ & ⦃G2, K2⦄ ⊢ ➡*[h, o] L2.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #HT12 #K1 #H @(lpxs_ind_dx … H) -K1
[ /2 width=5 by ex3_2_intro/
| #K1 #K #HK1 #_ * #L #T #HT1 #HT2 #HL2 -HT12
  lapply (lpx_cpxs_trans … HT1 … HK1) -HT1
  elim (lpx_fqup_trans … HT2 … HK1) -K
  /3 width=7 by lpxs_strap2, cpxs_trans, ex3_2_intro/
]
qed-.

lemma lpxs_fqus_trans: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐* ⦃G2, L2, T2⦄ →
                       ∀K1. ⦃G1, K1⦄ ⊢ ➡*[h, o] L1 →
                       ∃∃K2,T. ⦃G1, K1⦄ ⊢ T1 ➡*[h, o] T & ⦃G1, K1, T⦄ ⊐* ⦃G2, K2, T2⦄ & ⦃G2, K2⦄ ⊢ ➡*[h, o] L2.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H @(fqus_ind … H) -G2 -L2 -T2 /2 width=5 by ex3_2_intro/
#G #G2 #L #L2 #T #T2 #_ #H2 #IH1 #K1 #HLK1 elim (IH1 … HLK1) -L1
#L0 #T0 #HT10 #HT0 #HL0 elim (lpxs_fquq_trans … H2 … HL0) -L
#L #T3 #HT3 #HT32 #HL2 elim (fqus_cpxs_trans … HT3 … HT0) -T
/3 width=7 by cpxs_trans, fqus_strap1, ex3_2_intro/
qed-.
