lemma lprs_aaa_conf: ∀G,L1,T,A. ⦃G, L1⦄ ⊢ T ⁝ A →
                     ∀L2. ⦃G, L1⦄ ⊢ ➡* L2 → ⦃G, L2⦄ ⊢ T ⁝ A.
/3 width=5 by lprs_lpxs, lpxs_aaa_conf/ qed-.
