(*
lemma cprs_fpbs: ∀h,o,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡*[h] T2 → ⦃G, L, T1⦄ ≥[h, o] ⦃G, L, T2⦄.
/3 width=1 by cprs_cpxs, cpxs_fpbs/ qed.

lemma lprs_fpbs: ∀h,o,G,L1,L2,T. ⦃G, L1⦄ ⊢ ➡* L2 → ⦃G, L1, T⦄ ≥[h, o] ⦃G, L2, T⦄.
/3 width=1 by lprs_lpxs, lpxs_fpbs/ qed.

(* Note: this is used in the closure proof *)
lemma cpr_lpr_fpbs: ∀h,o,G,L1,L2,T1,T2. ⦃G, L1⦄ ⊢ T1 ➡ T2 → ⦃G, L1⦄ ⊢ ➡ L2 →
                    ⦃G, L1, T1⦄ ≥[h, o] ⦃G, L2, T2⦄.
/4 width=5 by fpbs_strap1, fpbq_fpbs, lpr_fpbq, cpr_fpbq/
qed.
*)
