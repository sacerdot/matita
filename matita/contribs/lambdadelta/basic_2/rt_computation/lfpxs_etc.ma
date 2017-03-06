(* Basic_2A1: was just: lprs_lpxs *)
lemma lprs_lfpxs: ∀h,o,G,L1,L2. ⦃G, L1⦄ ⊢ ➡* L2 → ⦃G, L1⦄ ⊢ ➡*[h, o] L2.
/3 width=3 by lpr_lpx, monotonic_TC/ qed.
