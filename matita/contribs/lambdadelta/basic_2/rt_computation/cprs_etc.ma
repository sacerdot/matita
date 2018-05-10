lemma lsubr_cprs_trans: ∀G. lsub_trans … (cprs G) lsubr.
/3 width=5 by lsubr_cpr_trans, CTC_lsub_trans/
qed-.

(* Basic_1: was: pr3_pr1 *)
lemma tprs_cprs: ∀G,L,T1,T2. ⦃G, ⋆⦄ ⊢ T1 ➡* T2 → ⦃G, L⦄ ⊢ T1 ➡* T2.
/2 width=3 by lsubr_cprs_trans/ qed.

(* Basic_1: was: nf2_pr3_unfold *)
lemma cprs_inv_cnr1: ∀G,L,T,U. ⦃G, L⦄ ⊢ T ➡* U → ⦃G, L⦄ ⊢ ➡ 𝐍⦃T⦄ → T = U.
#G #L #T #U #H @(cprs_ind_dx … H) -T //
#T0 #T #H1T0 #_ #IHT #H2T0
lapply (H2T0 … H1T0) -H1T0 #H destruct /2 width=1 by/
qed-.
