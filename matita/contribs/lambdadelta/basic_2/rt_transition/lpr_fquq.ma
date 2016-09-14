(* Properties on context-sensitive parallel reduction for terms *************)

lemma fqu_cpr_trans_dx: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ →
                        ∀U2. ⦃G2, L2⦄ ⊢ T2 ➡ U2 →
                        ∃∃L,U1. ⦃G1, L1⦄ ⊢ ➡ L & ⦃G1, L⦄ ⊢ T1 ➡ U1 & ⦃G1, L, U1⦄ ⊐ ⦃G2, L2, U2⦄.
#G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
/3 width=5 by fqu_lref_O, fqu_pair_sn, fqu_bind_dx, fqu_flat_dx, lpr_pair, cpr_pair_sn, cpr_atom, cpr_bind, cpr_flat, ex3_2_intro/
#G #L #K #U #T #k #HLK #HUT #U2 #HU2
elim (lift_total U2 0 (k+1)) #T2 #HUT2
lapply (cpr_lift … HU2 … HLK … HUT … HUT2) -HU2 -HUT /3 width=9 by fqu_drop, ex3_2_intro/
qed-.

lemma fquq_cpr_trans_dx: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄ →
                         ∀U2. ⦃G2, L2⦄ ⊢ T2 ➡ U2 →
                         ∃∃L,U1. ⦃G1, L1⦄ ⊢ ➡ L & ⦃G1, L⦄ ⊢ T1 ➡ U1 & ⦃G1, L, U1⦄ ⊐⸮ ⦃G2, L2, U2⦄.
#G1 #G2 #L1 #L2 #T1 #T2 #H #U2 #HTU2 elim (fquq_inv_gen … H) -H
[ #HT12 elim (fqu_cpr_trans_dx … HT12 … HTU2) /3 width=5 by fqu_fquq, ex3_2_intro/
| * #H1 #H2 #H3 destruct /2 width=5 by ex3_2_intro/
]
qed-.

lemma fqu_cpr_trans_sn: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ →
                        ∀U2. ⦃G2, L2⦄ ⊢ T2 ➡ U2 →
                        ∃∃L,U1. ⦃G1, L1⦄ ⊢ ➡ L & ⦃G1, L1⦄ ⊢ T1 ➡ U1 & ⦃G1, L, U1⦄ ⊐ ⦃G2, L2, U2⦄.
#G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
/3 width=5 by fqu_lref_O, fqu_pair_sn, fqu_bind_dx, fqu_flat_dx, lpr_pair, cpr_pair_sn, cpr_atom, cpr_bind, cpr_flat, ex3_2_intro/
#G #L #K #U #T #k #HLK #HUT #U2 #HU2
elim (lift_total U2 0 (k+1)) #T2 #HUT2
lapply (cpr_lift … HU2 … HLK … HUT … HUT2) -HU2 -HUT /3 width=9 by fqu_drop, ex3_2_intro/
qed-.

lemma fquq_cpr_trans_sn: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄ →
                         ∀U2. ⦃G2, L2⦄ ⊢ T2 ➡ U2 →
                         ∃∃L,U1. ⦃G1, L1⦄ ⊢ ➡ L & ⦃G1, L1⦄ ⊢ T1 ➡ U1 & ⦃G1, L, U1⦄ ⊐⸮ ⦃G2, L2, U2⦄.
#G1 #G2 #L1 #L2 #T1 #T2 #H #U2 #HTU2 elim (fquq_inv_gen … H) -H
[ #HT12 elim (fqu_cpr_trans_sn … HT12 … HTU2) /3 width=5 by fqu_fquq, ex3_2_intro/
| * #H1 #H2 #H3 destruct /2 width=5 by ex3_2_intro/
]
qed-.

lemma fqu_lpr_trans: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ →
                     ∀K2. ⦃G2, L2⦄ ⊢ ➡ K2 →
                     ∃∃K1,T. ⦃G1, L1⦄ ⊢ ➡ K1 & ⦃G1, L1⦄ ⊢ T1 ➡ T & ⦃G1, K1, T⦄ ⊐ ⦃G2, K2, T2⦄.
#G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
/3 width=5 by fqu_lref_O, fqu_pair_sn, fqu_flat_dx, lpr_pair, ex3_2_intro/
[ #a #I #G2 #L2 #V2 #T2 #X #H elim (lpr_inv_pair1 … H) -H
  #K2 #W2 #HLK2 #HVW2 #H destruct
  /3 width=5 by fqu_fquq, cpr_pair_sn, fqu_bind_dx, ex3_2_intro/
| #G #L1 #K1 #T1 #U1 #k #HLK1 #HTU1 #K2 #HK12
  elim (drop_lpr_trans … HLK1 … HK12) -HK12
  /3 width=7 by fqu_drop, ex3_2_intro/
]
qed-.

lemma fquq_lpr_trans: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄ →
                      ∀K2. ⦃G2, L2⦄ ⊢ ➡ K2 →
                      ∃∃K1,T. ⦃G1, L1⦄ ⊢ ➡ K1 & ⦃G1, L1⦄ ⊢ T1 ➡ T & ⦃G1, K1, T⦄ ⊐⸮ ⦃G2, K2, T2⦄.
#G1 #G2 #L1 #L2 #T1 #T2 #H #K2 #HLK2 elim (fquq_inv_gen … H) -H
[ #HT12 elim (fqu_lpr_trans … HT12 … HLK2) /3 width=5 by fqu_fquq, ex3_2_intro/
| * #H1 #H2 #H3 destruct /2 width=5 by ex3_2_intro/
]
qed-.
