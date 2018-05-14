(* Properties on subclosure *************************************************)

lemma snv_fqu_conf: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ →
                    ⦃G1, L1⦄ ⊢ T1 ¡[h, o] → ⦃G2, L2⦄ ⊢ T2 ¡[h, o].
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
[ #I1 #G1 #L1 #V1 #H
  elim (snv_inv_lref … H) -H #I2 #L2 #V2 #H #HV2
  lapply (drop_inv_O2 … H) -H #H destruct //
|2: *
|5,6: /3 width=8 by snv_inv_lift/
]
[1,3: #a #I #G1 #L1 #V1 #T1 #H elim (snv_inv_bind … H) -H //
|2,4: * #G1 #L1 #V1 #T1 #H
  [1,3: elim (snv_inv_appl … H) -H //
  |2,4: elim (snv_inv_cast … H) -H //
  ]
]
qed-.

lemma snv_fquq_conf: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄ →
                     ⦃G1, L1⦄ ⊢ T1 ¡[h, o] → ⦃G2, L2⦄ ⊢ T2 ¡[h, o].
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H elim (fquq_inv_gen … H) -H [|*]
/2 width=5 by snv_fqu_conf/
qed-.

lemma snv_fqup_conf: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄ →
                     ⦃G1, L1⦄ ⊢ T1 ¡[h, o] → ⦃G2, L2⦄ ⊢ T2 ¡[h, o].
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H @(fqup_ind … H) -G2 -L2 -T2
/3 width=5 by fqup_strap1, snv_fqu_conf/
qed-.

lemma snv_fqus_conf: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐* ⦃G2, L2, T2⦄ →
                     ⦃G1, L1⦄ ⊢ T1 ¡[h, o] → ⦃G2, L2⦄ ⊢ T2 ¡[h, o].
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H elim (fqus_inv_gen … H) -H [|*]
/2 width=5 by snv_fqup_conf/
qed-.
