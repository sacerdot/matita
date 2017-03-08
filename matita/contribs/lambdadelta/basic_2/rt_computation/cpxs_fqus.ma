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
