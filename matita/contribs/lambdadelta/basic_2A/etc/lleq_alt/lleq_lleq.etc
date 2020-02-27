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

include "basic_2/substitution/cpys_cpys.ma".
include "basic_2/substitution/lleq_ldrop.ma".

(* Advanced forward lemmas **************************************************)

lemma lleq_fwd_lref: ∀L1,L2. ∀d:ynat. ∀i:nat. L1 ⋕[#i, d] L2 →
                     ∨∨ |L1| ≤ i ∧ |L2| ≤ i
                      | yinj i < d
                      | ∃∃I1,I2,K1,K2,V. ⇩[i] L1 ≡ K1.ⓑ{I1}V &
                                         ⇩[i] L2 ≡ K2.ⓑ{I2}V &
                                         K1 ⋕[V, yinj 0] K2 & d ≤ yinj i.
#L1 #L2 #d #i * #HL12 #IH elim (lt_or_ge i (|L1|)) /3 width=3 by or3_intro0, conj/
elim (ylt_split i d) /2 width=1 by or3_intro1/ #Hdi #Hi
elim (ldrop_O1_lt … Hi) #I1 #K1 #V1 #HLK1
elim (ldrop_O1_lt L2 i) // -Hi #I2 #K2 #V2 #HLK2
lapply (ldrop_fwd_length_minus2 … HLK2) #H
lapply (ldrop_fwd_length_minus2 … HLK1) >HL12 <H -HL12 -H
#H lapply (injective_plus_l … H) -H #HK12
elim (lift_total V1 0 (i+1)) #W1 #HVW1
elim (lift_total V2 0 (i+1)) #W2 #HVW2
elim (IH W1) elim (IH W2) #_ #H2 #H1 #_
elim (cpys_inv_lref1_ldrop … (H1 ?) … HLK2 … HVW1) -H1
[ elim (cpys_inv_lref1_ldrop … (H2 ?) … HLK1 … HVW2) -H2 ]
/3 width=7 by cpys_subst, yle_inj/ -W1 -W2 #H12 #_ #_ #H21 #_ #_
lapply (cpys_antisym_eq … H12 … H21) -H12 -H21 #H destruct
@or3_intro2 @(ex4_5_intro … HLK1 HLK2) // @conj // -HK12
#V elim (lift_total V 0 (i+1))
#W #HVW elim (IH W) -IH #H12 #H21 @conj #H
[ elim (cpys_inv_lref1_ldrop … (H12 ?) … HLK2 … HVW) -H12 -H21
| elim (cpys_inv_lref1_ldrop … (H21 ?) … HLK1 … HVW) -H21 -H12
] [1,3: >yminus_Y_inj ] /3 width=7 by cpys_subst_Y2, yle_inj/
qed-.

lemma lleq_fwd_lref_dx: ∀L1,L2,d,i. L1 ⋕[#i, d] L2 →
                        ∀I2,K2,V. ⇩[i] L2 ≡ K2.ⓑ{I2}V →
                        i < d ∨
                        ∃∃I1,K1. ⇩[i] L1 ≡ K1.ⓑ{I1}V & K1 ⋕[V, 0] K2 & d ≤ i.
#L1 #L2 #d #i #H #I2 #K2 #V #HLK2 elim (lleq_fwd_lref … H) -H [ * || * ]
[ #_ #H elim (lt_refl_false i)
  lapply (ldrop_fwd_length_lt2 … HLK2) -HLK2
  /2 width=3 by lt_to_le_to_lt/ (**) (* full auto too slow *)
| /2 width=1 by or_introl/
| #I1 #I2 #K11 #K22 #V0 #HLK11 #HLK22 #HV0 #Hdi lapply (ldrop_mono … HLK22 … HLK2) -L2
  #H destruct /3 width=5 by ex3_2_intro, or_intror/
]
qed-.

lemma lleq_fwd_lref_sn: ∀L1,L2,d,i. L1 ⋕[#i, d] L2 →
                        ∀I1,K1,V. ⇩[i] L1 ≡ K1.ⓑ{I1}V →
                        i < d ∨
                        ∃∃I2,K2. ⇩[i] L2 ≡ K2.ⓑ{I2}V & K1 ⋕[V, 0] K2 & d ≤ i.
#L1 #L2 #d #i #HL12 #I1 #K1 #V #HLK1 elim (lleq_fwd_lref_dx L2 … d … HLK1) -HLK1
[2: * ] /4 width=6 by lleq_sym, ex3_2_intro, or_introl, or_intror/
qed-.

(* Advanced inversion lemmas ************************************************)

lemma lleq_inv_lref_ge_dx: ∀L1,L2,d,i. L1 ⋕[#i, d] L2 → d ≤ i →
                           ∀I2,K2,V. ⇩[i] L2 ≡ K2.ⓑ{I2}V →
                           ∃∃I1,K1. ⇩[i] L1 ≡ K1.ⓑ{I1}V & K1 ⋕[V, 0] K2.
#L1 #L2 #d #i #H #Hdi #I2 #K2 #V #HLK2 elim (lleq_fwd_lref_dx … H … HLK2) -L2
[ #H elim (ylt_yle_false … H Hdi)
| * /2 width=4 by ex2_2_intro/
]
qed-.

lemma lleq_inv_lref_ge_sn: ∀L1,L2,d,i. L1 ⋕[#i, d] L2 → d ≤ i →
                           ∀I1,K1,V. ⇩[i] L1 ≡ K1.ⓑ{I1}V →
                           ∃∃I2,K2. ⇩[i] L2 ≡ K2.ⓑ{I2}V & K1 ⋕[V, 0] K2.
#L1 #L2 #d #i #HL12 #Hdi #I1 #K1 #V #HLK1 elim (lleq_inv_lref_ge_dx L2 … Hdi … HLK1) -Hdi -HLK1
/3 width=4 by lleq_sym, ex2_2_intro/
qed-.

lemma lleq_inv_lref_ge_gen: ∀L1,L2,d,i. L1 ⋕[#i, d] L2 → d ≤ i →
                            ∀I1,I2,K1,K2,V1,V2.
                            ⇩[i] L1 ≡ K1.ⓑ{I1}V1 → ⇩[i] L2 ≡ K2.ⓑ{I2}V2 →
                            V1 = V2 ∧ K1 ⋕[V2, 0] K2.
#L1 #L2 #d #i #HL12 #Hdi #I1 #I2 #K1 #K2 #V1 #V2 #HLK1 #HLK2
elim (lleq_inv_lref_ge_sn … HL12 … HLK1) // -L1 -d
#J #Y #HY lapply (ldrop_mono … HY … HLK2) -L2 -i #H destruct /2 width=1 by conj/
qed-.

lemma lleq_inv_lref_ge: ∀L1,L2,d,i. L1 ⋕[#i, d] L2 → d ≤ i →
                        ∀I,K1,K2,V. ⇩[i] L1 ≡ K1.ⓑ{I}V → ⇩[i] L2 ≡ K2.ⓑ{I}V →
                        K1 ⋕[V, 0] K2.
#L1 #L2 #d #i #HL12 #Hdi #I #K1 #K2 #V #HLK1 #HLK2
elim (lleq_inv_lref_ge_gen … HL12 … HLK1 HLK2) //
qed-.

(* Advanced properties ******************************************************)

lemma lleq_dec: ∀T,L1,L2,d. Decidable (L1 ⋕[T, d] L2).
#T #L1 @(f2_ind … rfw … L1 T) -L1 -T
#n #IH #L1 * *
[ #k #Hn #L2 elim (eq_nat_dec (|L1|) (|L2|)) /3 width=1 by or_introl, lleq_sort/
| #i #Hn #L2 elim (eq_nat_dec (|L1|) (|L2|))
  [ #HL12 #d elim (ylt_split i d) /3 width=1 by lleq_skip, or_introl/
    #Hdi elim (lt_or_ge i (|L1|)) #HiL1
    elim (lt_or_ge i (|L2|)) #HiL2 /3 width=1 by or_introl, lleq_free/
    elim (ldrop_O1_lt … HiL2) #I2 #K2 #V2 #HLK2
    elim (ldrop_O1_lt … HiL1) #I1 #K1 #V1 #HLK1
    elim (eq_term_dec V2 V1)
    [ #H3 elim (IH K1 V1 … K2 0) destruct
      /3 width=8 by lleq_lref, ldrop_fwd_rfw, or_introl/
    ]
    -IH #H3 @or_intror
    #H elim (lleq_fwd_lref … H) -H [1,3,4,6: * ]
    [1,3: /3 width=4 by lt_to_le_to_lt, lt_refl_false/
    |5,6: /2 width=4 by ylt_yle_false/
    ]
    #Z1 #Z2 #Y1 #Y2 #X #HLY1 #HLY2 #HX #_
    lapply (ldrop_mono … HLY1 … HLK1) -HLY1 -HLK1
    lapply (ldrop_mono … HLY2 … HLK2) -HLY2 -HLK2
    #H2 #H1 destruct /2 width=1 by/
  ]
| #p #Hn #L2 elim (eq_nat_dec (|L1|) (|L2|)) /3 width=1 by or_introl, lleq_gref/
| #a #I #V #T #Hn #L2 #d destruct
  elim (IH L1 V … L2 d) /2 width=1 by/
  elim (IH (L1.ⓑ{I}V) T … (L2.ⓑ{I}V) (d+1)) -IH /3 width=1 by or_introl, lleq_bind/
  #H1 #H2 @or_intror
  #H elim (lleq_inv_bind … H) -H /2 width=1 by/
| #I #V #T #Hn #L2 #d destruct
  elim (IH L1 V … L2 d) /2 width=1 by/
  elim (IH L1 T … L2 d) -IH /3 width=1 by or_introl, lleq_flat/
  #H1 #H2 @or_intror
  #H elim (lleq_inv_flat … H) -H /2 width=1 by/
]
-n /4 width=3 by lleq_fwd_length, or_intror/
qed-.

(* Main properties **********************************************************)

theorem lleq_trans: ∀d,T. Transitive … (lleq d T).
#d #T #L1 #L * #HL1 #IH1 #L2 * #HL2 #IH2 /3 width=3 by conj, iff_trans/
qed-.

theorem lleq_canc_sn: ∀L,L1,L2,T,d. L ⋕[d, T] L1→ L ⋕[d, T] L2 → L1 ⋕[d, T] L2.
/3 width=3 by lleq_trans, lleq_sym/ qed-.

theorem lleq_canc_dx: ∀L1,L2,L,T,d. L1 ⋕[d, T] L → L2 ⋕[d, T] L → L1 ⋕[d, T] L2.
/3 width=3 by lleq_trans, lleq_sym/ qed-.

(* Inversion lemmas on negated lazy quivalence for local environments *******)

lemma nlleq_inv_bind: ∀a,I,L1,L2,V,T,d. (L1 ⋕[ⓑ{a,I}V.T, d] L2 → ⊥) →
                      (L1 ⋕[V, d] L2 → ⊥) ∨ (L1.ⓑ{I}V ⋕[T, ⫯d] L2.ⓑ{I}V → ⊥).
#a #I #L1 #L2 #V #T #d #H elim (lleq_dec V L1 L2 d)
/4 width=1 by lleq_bind, or_intror, or_introl/
qed-.

lemma nlleq_inv_flat: ∀I,L1,L2,V,T,d. (L1 ⋕[ⓕ{I}V.T, d] L2 → ⊥) →
                      (L1 ⋕[V, d] L2 → ⊥) ∨ (L1 ⋕[T, d] L2 → ⊥).
#I #L1 #L2 #V #T #d #H elim (lleq_dec V L1 L2 d)
/4 width=1 by lleq_flat, or_intror, or_introl/
qed-.

(* Note: lleq_nlleq_trans: ∀d,T,L1,L. L1⋕[T, d] L →
                           ∀L2. (L ⋕[T, d] L2 → ⊥) → (L1 ⋕[T, d] L2 → ⊥).
/3 width=3 by lleq_canc_sn/ qed-.
works with /4 width=8/ so lleq_canc_sn is more convenient
*)
