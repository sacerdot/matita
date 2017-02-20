(*
lemma csx_tdeq_trans: ∀h,o,G,L,T1. ⦃G, L⦄ ⊢ ⬈[h, o] 𝐒⦃T1⦄ →
                      ∀T2. T1 ≡[h, o] T2 → ⦃G, L⦄ ⊢ ⬈[h, o] 𝐒⦃T2⦄.
#h #o #G #L #T1 #H @(csx_ind … H) -H #T #HT #IH #T2 #HT2
@csx_intro #T0 #HT20 #HnT20      

lemma csx_tdeq_trans: ∀h,o,T1,T2. T1 ≡[h, o] T2 →  
                      ∀G,L. ⦃G, L⦄ ⊢ ⬈[h, o] 𝐒⦃T1⦄ → ⦃G, L⦄ ⊢ ⬈[h, o] 𝐒⦃T2⦄.
#h #o #T1 #T2 #H elim H -T1 -T2 //
[ #s1 #s2 #d #Hs1 #Hs2 #G #L #H
| #I #V1 #V2 #T1 #T2 #_ #_ #IHV #IHT #G #L #H   

lemma csx_cpx_trans: ∀h,o,G,L,T1. ⦃G, L⦄ ⊢ ⬈[h, o] 𝐒⦃T1⦄ →
                     ∀T2. ⦃G, L⦄ ⊢ T1 ⬈[h] T2 → ⦃G, L⦄ ⊢ ⬈[h, o] 𝐒⦃T2⦄.
#h #o #G #L #T1 #H @(csx_ind … H) -T1 #T1 #HT1 #IHT1 #T2 #HLT12
elim (tdeq_dec h o T1 T2) #HT12 /3 width=4 by/ -IHT1 -HLT12
qed-.

(* Basic_1: was just: sn3_cast *)
lemma csx_cast: ∀h,o,G,L,W. ⦃G, L⦄ ⊢ ⬈[h, o] 𝐒⦃W →
                ∀T. ⦃G, L⦄ ⊢ ⬈[h, o] 𝐒⦃T → ⦃G, L⦄ ⊢ ⬈[h, o] 𝐒⦃ⓝW.T.
#h #o #G #L #W #HW @(csx_ind … HW) -W #W #HW #IHW #T #HT @(csx_ind … HT) -T #T #HT #IHT
@csx_intro #X #H1 #H2
elim (cpx_inv_cast1 … H1) -H1
[ * #W0 #T0 #HLW0 #HLT0 #H destruct
  elim (eq_false_inv_tpair_sn … H2) -H2
  [ /3 width=3 by csx_cpx_trans/
  | -HLW0 * #H destruct /3 width=1 by/
  ]
|2,3: /3 width=3 by csx_cpx_trans/
]
qed.

*)
