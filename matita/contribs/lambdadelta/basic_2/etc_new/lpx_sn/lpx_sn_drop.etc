definition dropable_dx: predicate (relation lenv) ≝
                        λR. ∀L1,L2. R L1 L2 → ∀K2,c,k. ⬇[c, 0, k] L2 ≡ K2 →
                        ∃∃K1. ⬇[c, 0, k] L1 ≡ K1 & R K1 K2.

lemma dropable_dx_TC: ∀R. dropable_dx R → dropable_dx (TC … R).
#R #HR #L1 #L2 #H elim H -L2
[ #L2 #HL12 #K2 #c #k #HLK2 elim (HR … HL12 … HLK2) -HR -L2
  /3 width=3 by inj, ex2_intro/
| #L #L2 #_ #HL2 #IHL1 #K2 #c #k #HLK2 elim (HR … HL2 … HLK2) -HR -L2
  #K #HLK #HK2 elim (IHL1 … HLK) -L
  /3 width=5 by step, ex2_intro/
]
qed-.


fact lpx_sn_dropable_aux: ∀R,L2,K2,c,l,k. ⬇[c, l, k] L2 ≡ K2 → ∀L1. lpx_sn R L1 L2 →
                          l = 0 → ∃∃K1. ⬇[c, 0, k] L1 ≡ K1 & lpx_sn R K1 K2.
#R #L2 #K2 #c #l #k #H elim H -L2 -K2 -l -k
[ #l #k #Hm #X #H >(lpx_sn_inv_atom2 … H) -H
  /4 width=3 by drop_atom, lpx_sn_atom, ex2_intro/
| #I #K2 #V2 #X #H elim (lpx_sn_inv_pair2 … H) -H
  #K1 #V1 #HK12 #HV12 #H destruct
  /3 width=5 by drop_pair, lpx_sn_pair, ex2_intro/
| #I #L2 #K2 #V2 #k #_ #IHLK2 #X #H #_ elim (lpx_sn_inv_pair2 … H) -H
  #L1 #V1 #HL12 #HV12 #H destruct
  elim (IHLK2 … HL12) -L2 /3 width=3 by drop_drop, ex2_intro/
| #I #L2 #K2 #V2 #W2 #l #k #_ #_ #_ #L1 #_ #H elim (ysucc_inv_O_dx … H)
]
qed-.

lemma lpx_sn_dropable: ∀R. dropable_dx (lpx_sn R).
/2 width=5 by lpx_sn_dropable_aux/ qed-.

lemma lpx_sn_drop_trans: ∀R,L1,L2. lpx_sn R L1 L2 →
                         ∀I,K2,V2,i. ⬇[i] L2 ≡ K2.ⓑ{I}V2 →
                         ∃∃K1,V1. ⬇[i] L1 ≡ K1.ⓑ{I}V1 & lpx_sn R K1 K2 & R K1 V1 V2.
#R #L1 #L2 #H elim H -L1 -L2
[ #I0 #K0 #V0 #i #H elim (drop_inv_atom1 … H) -H #H destruct
| #I #K1 #K2 #V1 #V2 #HK12 #HV12 #IHK12 #I0 #K0 #V0 #i #H elim (drop_inv_O1_pair1 … H) * -H
  [ -IHK12 #H1 #H2 destruct /3 width=5 by drop_pair, ex3_2_intro/
  | -HK12 -HV12 #Hi #HK10 elim (IHK12 … HK10) -IHK12 -HK10
    /3 width=5 by drop_drop_lt, ex3_2_intro/
  ]
]
qed-.

lemma lpx_sn_drop_conf: ∀R,L1,L2. lpx_sn R L1 L2 →
                        ∀I,K1,V1,i. ⬇[i] L1 ≡ K1.ⓑ{I}V1 →
                        ∃∃K2,V2. ⬇[i] L2 ≡ K2.ⓑ{I}V2 & lpx_sn R K1 K2 & R K1 V1 V2.
#R #L1 #L2 #H elim H -L1 -L2
[ #I0 #K0 #V0 #i #H elim (drop_inv_atom1 … H) -H #H destruct
| #I #K1 #K2 #V1 #V2 #HK12 #HV12 #IHK12 #I0 #K0 #V0 #i #H elim (drop_inv_O1_pair1 … H) * -H
  [ -IHK12 #H1 #H2 destruct /3 width=5 by drop_pair, ex3_2_intro/
  | -HK12 -HV12 #Hi #HK10 elim (IHK12 … HK10) -IHK12 -HK10
    /3 width=5 by drop_drop_lt, ex3_2_intro/
  ]
]
qed-.
