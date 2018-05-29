include "basic_2/rt_computation/lprs.ma".

lemma lprs_lpxs: ∀h,g,G,L1,L2. ⦃G, L1⦄ ⊢ ➡* L2 → ⦃G, L1⦄ ⊢ ➡*[h, g] L2.
/3 width=3 by lpr_lpx, monotonic_TC/ qed.
