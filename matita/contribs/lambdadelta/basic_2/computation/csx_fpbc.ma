include "basic_2/computation/fpbc.ma".

(* Advanced eliminators *****************************************************)

fact csx_ind_fpbc_aux: ∀h,g. ∀R:relation3 genv lenv term.
                       (∀G1,L1,T1. ⦃G1, L1⦄ ⊢ ⬊*[h, g] T1 →
                                   (∀G2,L2,T2. ⦃G1, L1, T1⦄ ≻[h, g] ⦃G2, L2, T2⦄ → R G2 L2 T2) →
                                   R G1 L1 T1
                       ) →
                       ∀G1,L1,T1. ⦃G1, L1⦄ ⊢ ⬊*[h, g] T1 →
                       ∀G2,L2,T2. ⦃G1, L1, T1⦄ ⊃* ⦃G2, L2, T2⦄ → R G2 L2 T2.
#h #g #R #IH1 #G1 #L1 #T1 #H @(csx_ind … H) -T1
#T1 @(fqup_wf_ind … G1 L1 T1) -G1 -L1 -T1
#G1 #L1 #T1 #IH2 #H1 #IH3 #G2 #L2 #T2 #H12 @IH1 -IH1 /2 width=5 by csx_fqus_conf/
#G #L #T *
[ #G0 #L0 #T0 #H20 lapply (fqus_fqup_trans … H12 H20) -G2 -L2 -T2
  #H10 @(IH2 … H10) -IH2 /2 width=5 by csx_fqup_conf/
  #T2 #HT02 #H #G3 #L3 #T3 #HT23 elim (fqup_cpx_trans_neq … H10 … HT02 H) -T0
  /4 width=8 by fqup_fqus_trans, fqup_fqus/
| #T0 #HT20 #H elim (fqus_cpxs_trans_neq … H12 … HT20 H) -T2 /3 width=4 by/
]
qed-.

lemma csx_ind_fpbc: ∀h,g. ∀R:relation3 genv lenv term.
                    (∀G1,L1,T1. ⦃G1, L1⦄ ⊢ ⬊*[h, g] T1 →
                                (∀G2,L2,T2. ⦃G1, L1, T1⦄ ≻[h, g] ⦃G2, L2, T2⦄ → R G2 L2 T2) →
                                R G1 L1 T1
                    ) →
                    ∀G,L,T. ⦃G, L⦄ ⊢ ⬊*[h, g] T → R G L T.
/4 width=8 by csx_ind_fpbc_fqus/ qed-.
