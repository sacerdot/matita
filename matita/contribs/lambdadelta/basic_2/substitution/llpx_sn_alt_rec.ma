(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "basic_2/relocation/lift_neg.ma".
include "basic_2/relocation/ldrop_ldrop.ma".
include "basic_2/substitution/llpx_sn.ma".

(* LAZY SN POINTWISE EXTENSION OF A CONTEXT-SENSITIVE REALTION FOR TERMS ****)

(* alternative definition of llpx_sn (recursive) *)
inductive llpx_sn_alt_r (R:relation4 bind2 lenv term term): relation4 ynat term lenv lenv ≝
| llpx_sn_alt_r_intro: ∀L1,L2,T,d.
                       (∀I1,I2,K1,K2,V1,V2,i. d ≤ yinj i → (∀U. ⇧[i, 1] U ≡ T → ⊥) →
                          ⇩[i] L1 ≡ K1.ⓑ{I1}V1 → ⇩[i] L2 ≡ K2.ⓑ{I2}V2 → I1 = I2 ∧ R I1 K1 V1 V2
                       ) →
                       (∀I1,I2,K1,K2,V1,V2,i. d ≤ yinj i → (∀U. ⇧[i, 1] U ≡ T → ⊥) →
                          ⇩[i] L1 ≡ K1.ⓑ{I1}V1 → ⇩[i] L2 ≡ K2.ⓑ{I2}V2 → llpx_sn_alt_r R 0 V1 K1 K2
                       ) → |L1| = |L2| → llpx_sn_alt_r R d T L1 L2
.

(* Compact definition of llpx_sn_alt_r **************************************)

lemma llpx_sn_alt_r_intro_alt: ∀R,L1,L2,T,d. |L1| = |L2| →
                               (∀I1,I2,K1,K2,V1,V2,i. d ≤ yinj i → (∀U. ⇧[i, 1] U ≡ T → ⊥) →
                                  ⇩[i] L1 ≡ K1.ⓑ{I1}V1 → ⇩[i] L2 ≡ K2.ⓑ{I2}V2 →
                                  ∧∧ I1 = I2 & R I1 K1 V1 V2 & llpx_sn_alt_r R 0 V1 K1 K2
                               ) → llpx_sn_alt_r R d T L1 L2.
#R #L1 #L2 #T #d #HL12 #IH @llpx_sn_alt_r_intro // -HL12
#I1 #I2 #K1 #K2 #V1 #V2 #i #Hid #HnT #HLK1 #HLK2
elim (IH … HnT HLK1 HLK2) -IH -HnT -HLK1 -HLK2 /2 width=1 by conj/
qed.

lemma llpx_sn_alt_r_ind_alt: ∀R. ∀S:relation4 ynat term lenv lenv.
                             (∀L1,L2,T,d. |L1| = |L2| → (
                                ∀I1,I2,K1,K2,V1,V2,i. d ≤ yinj i → (∀U. ⇧[i, 1] U ≡ T → ⊥) →
                                ⇩[i] L1 ≡ K1.ⓑ{I1}V1 → ⇩[i] L2 ≡ K2.ⓑ{I2}V2 →
                                ∧∧ I1 = I2 & R I1 K1 V1 V2 & llpx_sn_alt_r R 0 V1 K1 K2 & S 0 V1 K1 K2
                             ) → S d T L1 L2) →
                             ∀L1,L2,T,d. llpx_sn_alt_r R d T L1 L2 → S d T L1 L2.
#R #S #IH #L1 #L2 #T #d #H elim H -L1 -L2 -T -d
#L1 #L2 #T #d #H1 #H2 #HL12 #IH2 @IH -IH // -HL12
#I1 #I2 #K1 #K2 #V1 #V2 #i #Hid #HnT #HLK1 #HLK2
elim (H1 … HnT HLK1 HLK2) -H1 /4 width=8 by and4_intro/
qed-.

lemma llpx_sn_alt_r_inv_alt: ∀R,L1,L2,T,d. llpx_sn_alt_r R d T L1 L2 →
                             |L1| = |L2| ∧
                             ∀I1,I2,K1,K2,V1,V2,i. d ≤ yinj i → (∀U. ⇧[i, 1] U ≡ T → ⊥) →
                             ⇩[i] L1 ≡ K1.ⓑ{I1}V1 → ⇩[i] L2 ≡ K2.ⓑ{I2}V2 →
                             ∧∧ I1 = I2 & R I1 K1 V1 V2 & llpx_sn_alt_r R 0 V1 K1 K2.
#R #L1 #L2 #T #d #H @(llpx_sn_alt_r_ind_alt … H) -L1 -L2 -T -d
#L1 #L2 #T #d #HL12 #IH @conj // -HL12
#I1 #I2 #K1 #K2 #V1 #V2 #i #Hid #HnT #HLK1 #HLK2
elim (IH … HnT HLK1 HLK2) -IH -HnT -HLK1 -HLK2 /2 width=1 by and3_intro/
qed-.

(* Basic inversion lemmas ***************************************************)

lemma llpx_sn_alt_r_inv_flat: ∀R,I,L1,L2,V,T,d. llpx_sn_alt_r R d (ⓕ{I}V.T) L1 L2 →
                              llpx_sn_alt_r R d V L1 L2 ∧ llpx_sn_alt_r R d T L1 L2.
#R #I #L1 #L2 #V #T #d #H elim (llpx_sn_alt_r_inv_alt … H) -H
#HL12 #IH @conj @llpx_sn_alt_r_intro_alt // -HL12
#I1 #I2 #K1 #K2 #V1 #V2 #i #Hdi #H #HLK1 #HLK2
elim (IH … HLK1 HLK2) -IH -HLK1 -HLK2 //
/3 width=8 by nlift_flat_sn, nlift_flat_dx, and3_intro/
qed-.

lemma llpx_sn_alt_r_inv_bind: ∀R,a,I,L1,L2,V,T,d. llpx_sn_alt_r R d (ⓑ{a,I}V.T) L1 L2 →
                              llpx_sn_alt_r R d V L1 L2 ∧ llpx_sn_alt_r R (⫯d) T (L1.ⓑ{I}V) (L2.ⓑ{I}V).
#R #a #I #L1 #L2 #V #T #d #H elim (llpx_sn_alt_r_inv_alt … H) -H
#HL12 #IH @conj @llpx_sn_alt_r_intro_alt [1,3: normalize // ] -HL12
#I1 #I2 #K1 #K2 #V1 #V2 #i #Hdi #H #HLK1 #HLK2
[ elim (IH … HLK1 HLK2) -IH -HLK1 -HLK2
  /3 width=9 by nlift_bind_sn, and3_intro/
| lapply (yle_inv_succ1 … Hdi) -Hdi * #Hdi #Hi
  lapply (ldrop_inv_drop1_lt … HLK1 ?) -HLK1 /2 width=1 by ylt_O/ #HLK1
  lapply (ldrop_inv_drop1_lt … HLK2 ?) -HLK2 /2 width=1 by ylt_O/ #HLK2
  elim (IH … HLK1 HLK2) -IH -HLK1 -HLK2 /2 width=1 by and3_intro/
  @nlift_bind_dx <plus_minus_m_m /2 width=2 by ylt_O/
]
qed-.

(* Basic forward lemmas *****************************************************)

lemma llpx_sn_alt_r_fwd_length: ∀R,L1,L2,T,d. llpx_sn_alt_r R d T L1 L2 → |L1| = |L2|.
#R #L1 #L2 #T #d #H elim (llpx_sn_alt_r_inv_alt … H) -H //
qed-.

lemma llpx_sn_alt_r_fwd_lref: ∀R,L1,L2,d,i. llpx_sn_alt_r R d (#i) L1 L2 →
                              ∨∨ |L1| ≤ i ∧ |L2| ≤ i
                               | yinj i < d
                               | ∃∃I,K1,K2,V1,V2. ⇩[i] L1 ≡ K1.ⓑ{I}V1 &
                                                  ⇩[i] L2 ≡ K2.ⓑ{I}V2 &
                                                  llpx_sn_alt_r R (yinj 0) V1 K1 K2 &
                                                  R I K1 V1 V2 & d ≤ yinj i.
#R #L1 #L2 #d #i #H elim (llpx_sn_alt_r_inv_alt … H) -H
#HL12 #IH elim (lt_or_ge i (|L1|)) /3 width=1 by or3_intro0, conj/
elim (ylt_split i d) /3 width=1 by or3_intro1/
#Hdi #HL1 elim (ldrop_O1_lt (Ⓕ) … HL1)
#I1 #K1 #V1 #HLK1 elim (ldrop_O1_lt (Ⓕ) L2 i) //
#I2 #K2 #V2 #HLK2 elim (IH … HLK1 HLK2) -IH
/3 width=9 by nlift_lref_be_SO, or3_intro2, ex5_5_intro/
qed-.

(* Basic properties *********************************************************)

lemma llpx_sn_alt_r_sort: ∀R,L1,L2,d,k. |L1| = |L2| → llpx_sn_alt_r R d (⋆k) L1 L2.
#R #L1 #L2 #d #k #HL12 @llpx_sn_alt_r_intro_alt // -HL12
#I1 #I2 #K1 #K2 #V1 #V2 #i #_ #H elim (H (⋆k)) //
qed.

lemma llpx_sn_alt_r_gref: ∀R,L1,L2,d,p. |L1| = |L2| → llpx_sn_alt_r R d (§p) L1 L2.
#R #L1 #L2 #d #p #HL12 @llpx_sn_alt_r_intro_alt // -HL12
#I1 #I2 #K1 #K2 #V1 #V2 #i #_ #H elim (H (§p)) //
qed.

lemma llpx_sn_alt_r_skip: ∀R,L1,L2,d,i. |L1| = |L2| → yinj i < d → llpx_sn_alt_r R d (#i) L1 L2.
#R #L1 #L2 #d #i #HL12 #Hid @llpx_sn_alt_r_intro_alt // -HL12
#I1 #I2 #K1 #K2 #V1 #V2 #j #Hdj #H elim (H (#i)) -H
/4 width=3 by lift_lref_lt, ylt_yle_trans, ylt_inv_inj/
qed.

lemma llpx_sn_alt_r_free: ∀R,L1,L2,d,i. |L1| ≤ i → |L2| ≤ i → |L1| = |L2| →
                          llpx_sn_alt_r R d (#i) L1 L2.
#R #L1 #L2 #d #i #HL1 #_ #HL12 @llpx_sn_alt_r_intro_alt // -HL12
#I1 #I2 #K1 #K2 #V1 #V2 #j #_ #H #HLK1 elim (H (#(i-1))) -H
lapply (ldrop_fwd_length_lt2 … HLK1) -HLK1
/3 width=3 by lift_lref_ge_minus, lt_to_le_to_lt/
qed.

lemma llpx_sn_alt_r_lref: ∀R,I,L1,L2,K1,K2,V1,V2,d,i. d ≤ yinj i →
                          ⇩[i] L1 ≡ K1.ⓑ{I}V1 → ⇩[i] L2 ≡ K2.ⓑ{I}V2 →
                          llpx_sn_alt_r R 0 V1 K1 K2 → R I K1 V1 V2 →
                          llpx_sn_alt_r R d (#i) L1 L2.
#R #I #L1 #L2 #K1 #K2 #V1 #V2 #d #i #Hdi #HLK1 #HLK2 #HK12 #HV12 @llpx_sn_alt_r_intro_alt
[ lapply (llpx_sn_alt_r_fwd_length … HK12) -HK12 #HK12
  @(ldrop_fwd_length_eq2 … HLK1 HLK2) normalize //
| #Z1 #Z2 #Y1 #Y2 #X1 #X2 #j #Hdj #H #HLY1 #HLY2
  elim (lt_or_eq_or_gt i j) #Hij destruct
  [ elim (H (#i)) -H /2 width=1 by lift_lref_lt/
  | lapply (ldrop_mono … HLY1 … HLK1) -HLY1 -HLK1 #H destruct
    lapply (ldrop_mono … HLY2 … HLK2) -HLY2 -HLK2 #H destruct /2 width=1 by and3_intro/
  | elim (H (#(i-1))) -H /2 width=1 by lift_lref_ge_minus/
  ]
]
qed.

lemma llpx_sn_alt_r_flat: ∀R,I,L1,L2,V,T,d.
                          llpx_sn_alt_r R d V L1 L2 → llpx_sn_alt_r R d T L1 L2 →
                          llpx_sn_alt_r R d (ⓕ{I}V.T) L1 L2.
#R #I #L1 #L2 #V #T #d #HV #HT
elim (llpx_sn_alt_r_inv_alt … HV) -HV #HL12 #IHV
elim (llpx_sn_alt_r_inv_alt … HT) -HT #_ #IHT
@llpx_sn_alt_r_intro_alt // -HL12
#I1 #I2 #K1 #K2 #V1 #V2 #i #Hdi #HnVT #HLK1 #HLK2
elim (nlift_inv_flat … HnVT) -HnVT #H
[ elim (IHV … HLK1 … HLK2) -IHV /2 width=2 by and3_intro/
| elim (IHT … HLK1 … HLK2) -IHT /3 width=2 by and3_intro/
]
qed.

lemma llpx_sn_alt_r_bind: ∀R,a,I,L1,L2,V,T,d.
                          llpx_sn_alt_r R d V L1 L2 →
                          llpx_sn_alt_r R (⫯d) T (L1.ⓑ{I}V) (L2.ⓑ{I}V) →
                          llpx_sn_alt_r R d (ⓑ{a,I}V.T) L1 L2.
#R #a #I #L1 #L2 #V #T #d #HV #HT
elim (llpx_sn_alt_r_inv_alt … HV) -HV #HL12 #IHV
elim (llpx_sn_alt_r_inv_alt … HT) -HT #_ #IHT
@llpx_sn_alt_r_intro_alt // -HL12
#I1 #I2 #K1 #K2 #V1 #V2 #i #Hdi #HnVT #HLK1 #HLK2
elim (nlift_inv_bind … HnVT) -HnVT #H
[ elim (IHV … HLK1 … HLK2) -IHV /2 width=2 by and3_intro/
| elim IHT -IHT /2 width=12 by ldrop_drop, yle_succ, and3_intro/
]
qed.

(* Main properties **********************************************************)

theorem llpx_sn_lpx_sn_alt_r: ∀R,L1,L2,T,d. llpx_sn R d T L1 L2 → llpx_sn_alt_r R d T L1 L2.
#R #L1 #L2 #T #d #H elim H -L1 -L2 -T -d
/2 width=9 by llpx_sn_alt_r_sort, llpx_sn_alt_r_gref, llpx_sn_alt_r_skip, llpx_sn_alt_r_free, llpx_sn_alt_r_lref, llpx_sn_alt_r_flat, llpx_sn_alt_r_bind/
qed.

(* Main inversion lemmas ****************************************************)

theorem llpx_sn_alt_r_inv_lpx_sn: ∀R,T,L1,L2,d. llpx_sn_alt_r R d T L1 L2 → llpx_sn R d T L1 L2.
#R #T #L1 @(f2_ind … rfw … L1 T) -L1 -T #n #IH #L1 * *
[1,3: /3 width=4 by llpx_sn_alt_r_fwd_length, llpx_sn_gref, llpx_sn_sort/
| #i #Hn #L2 #d #H lapply (llpx_sn_alt_r_fwd_length … H)
  #HL12 elim (llpx_sn_alt_r_fwd_lref … H) -H
  [ * /2 width=1 by llpx_sn_free/
  | /2 width=1 by llpx_sn_skip/
  | * /4 width=9 by llpx_sn_lref, ldrop_fwd_rfw/
  ]
| #a #I #V #T #Hn #L2 #d #H elim (llpx_sn_alt_r_inv_bind … H) -H
  /3 width=1 by llpx_sn_bind/
| #I #V #T #Hn #L2 #d #H elim (llpx_sn_alt_r_inv_flat … H) -H
  /3 width=1 by llpx_sn_flat/
]
qed-.

(* Alternative definition of llpx_sn (recursive) ****************************)

lemma llpx_sn_intro_alt_r: ∀R,L1,L2,T,d. |L1| = |L2| →
                           (∀I1,I2,K1,K2,V1,V2,i. d ≤ yinj i → (∀U. ⇧[i, 1] U ≡ T → ⊥) →
                              ⇩[i] L1 ≡ K1.ⓑ{I1}V1 → ⇩[i] L2 ≡ K2.ⓑ{I2}V2 →
                              ∧∧ I1 = I2 & R I1 K1 V1 V2 & llpx_sn R 0 V1 K1 K2
                           ) → llpx_sn R d T L1 L2.
#R #L1 #L2 #T #d #HL12 #IH @llpx_sn_alt_r_inv_lpx_sn
@llpx_sn_alt_r_intro_alt // -HL12
#I1 #I2 #K1 #K2 #V1 #V2 #i #Hid #HnT #HLK1 #HLK2
elim (IH … HnT HLK1 HLK2) -IH -HnT -HLK1 -HLK2 /3 width=1 by llpx_sn_lpx_sn_alt_r, and3_intro/
qed.

lemma llpx_sn_ind_alt_r: ∀R. ∀S:relation4 ynat term lenv lenv.
                         (∀L1,L2,T,d. |L1| = |L2| → (
                            ∀I1,I2,K1,K2,V1,V2,i. d ≤ yinj i → (∀U. ⇧[i, 1] U ≡ T → ⊥) →
                            ⇩[i] L1 ≡ K1.ⓑ{I1}V1 → ⇩[i] L2 ≡ K2.ⓑ{I2}V2 →
                            ∧∧ I1 = I2 & R I1 K1 V1 V2 & llpx_sn R 0 V1 K1 K2 & S 0 V1 K1 K2
                         ) → S d T L1 L2) →
                         ∀L1,L2,T,d. llpx_sn R d T L1 L2 → S d T L1 L2.
#R #S #IH1 #L1 #L2 #T #d #H lapply (llpx_sn_lpx_sn_alt_r … H) -H
#H @(llpx_sn_alt_r_ind_alt … H) -L1 -L2 -T -d
#L1 #L2 #T #d #HL12 #IH2 @IH1 -IH1 // -HL12
#I1 #I2 #K1 #K2 #V1 #V2 #i #Hid #HnT #HLK1 #HLK2
elim (IH2 … HnT HLK1 HLK2) -IH2 -HnT -HLK1 -HLK2 /3 width=1 by llpx_sn_alt_r_inv_lpx_sn, and4_intro/
qed-.

lemma llpx_sn_inv_alt_r: ∀R,L1,L2,T,d. llpx_sn R d T L1 L2 →
                         |L1| = |L2| ∧
                         ∀I1,I2,K1,K2,V1,V2,i. d ≤ yinj i → (∀U. ⇧[i, 1] U ≡ T → ⊥) →
                         ⇩[i] L1 ≡ K1.ⓑ{I1}V1 → ⇩[i] L2 ≡ K2.ⓑ{I2}V2 →
                         ∧∧ I1 = I2 & R I1 K1 V1 V2 & llpx_sn R 0 V1 K1 K2.
#R #L1 #L2 #T #d #H lapply (llpx_sn_lpx_sn_alt_r … H) -H
#H elim (llpx_sn_alt_r_inv_alt … H) -H
#HL12 #IH @conj //
#I1 #I2 #K1 #K2 #V1 #V2 #i #Hid #HnT #HLK1 #HLK2
elim (IH … HnT HLK1 HLK2) -IH -HnT -HLK1 -HLK2 /3 width=1 by llpx_sn_alt_r_inv_lpx_sn, and3_intro/
qed-.
