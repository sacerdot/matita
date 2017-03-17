lemma csx_fqu_conf: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ →
                    ⦃G1, L1⦄ ⊢ ⬈*[h, o] T1 → ⦃G2, L2⦄ ⊢ ⬈*[h, o] T2.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
/2 width=8 by csx_inv_lref_bind, csx_inv_lift, csx_fwd_flat_dx, csx_fwd_bind_dx, csx_fwd_pair_sn/
qed-.

lemma csx_fquq_conf: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄ →
                     ⦃G1, L1⦄ ⊢ ⬈*[h, o] T1 → ⦃G2, L2⦄ ⊢ ⬈*[h, o] T2.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H12 #H elim (fquq_inv_gen … H12) -H12
[ /2 width=5 by csx_fqu_conf/
| * #HG #HL #HT destruct //
]
qed-.

lemma csx_fqup_conf: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄ →
                     ⦃G1, L1⦄ ⊢ ⬈*[h, o] T1 → ⦃G2, L2⦄ ⊢ ⬈*[h, o] T2.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H @(fqup_ind … H) -G2 -L2 -T2
/3 width=5 by csx_fqu_conf/
qed-.

lemma csx_fqus_conf: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐* ⦃G2, L2, T2⦄ →
                     ⦃G1, L1⦄ ⊢ ⬈*[h, o] T1 → ⦃G2, L2⦄ ⊢ ⬈*[h, o] T2.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H12 #H elim (fqus_inv_gen … H12) -H12
[ /2 width=5 by csx_fqup_conf/
| * #HG #HL #HT destruct //
]
qed-.

