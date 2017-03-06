(* Basic forward lemmas *****************************************************)

(* Forward lemmas with length for local environments ************************)

(* Basic_2A1: was just: lpxs_fwd_length *)
lemma lfpxs_fwd_length: ∀h,o,G,L1,L2. ⦃G, L1⦄ ⊢ ⬈*[h, o] L2 → |L1| = |L2|.
/2 width=2 by TC_lpx_sn_fwd_length/ qed-.
