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

notation "hvbox( L ⊢ break term 46 T1 break ▶ [ term 46 d , break term 46 e ] break term 46 T2 )"
   non associative with precedence 45
   for @{ 'PSubst $L $T1 $d $e $T2 }.

include "basic_2/substitution/ldrop_append.ma".

(* PARALLEL SUBSTITUTION ON TERMS *******************************************)

inductive tps: nat → nat → lenv → relation term ≝
| tps_atom : ∀L,I,d,e. tps d e L (⓪{I}) (⓪{I})
| tps_subst: ∀L,K,V,W,i,d,e. d ≤ i → i < d + e →
             ⇩[0, i] L ≡ K. ⓓV → ⇧[0, i + 1] V ≡ W → tps d e L (#i) W
| tps_bind : ∀L,a,I,V1,V2,T1,T2,d,e.
             tps d e L V1 V2 → tps (d + 1) e (L. ⓑ{I} V2) T1 T2 →
             tps d e L (ⓑ{a,I} V1. T1) (ⓑ{a,I} V2. T2)
| tps_flat : ∀L,I,V1,V2,T1,T2,d,e.
             tps d e L V1 V2 → tps d e L T1 T2 →
             tps d e L (ⓕ{I} V1. T1) (ⓕ{I} V2. T2)
.

interpretation "parallel substritution (term)"
   'PSubst L T1 d e T2 = (tps d e L T1 T2).

(* Basic properties *********************************************************)

lemma tps_lsubr_trans: ∀L1,T1,T2,d,e. L1 ⊢ T1 ▶ [d, e] T2 →
                       ∀L2. L2 ⊑ [d, e] L1 → L2 ⊢ T1 ▶ [d, e] T2.
#L1 #T1 #T2 #d #e #H elim H -L1 -T1 -T2 -d -e
[ //
| #L1 #K1 #V #W #i #d #e #Hdi #Hide #HLK1 #HVW #L2 #HL12
  elim (ldrop_lsubr_ldrop2_abbr … HL12 … HLK1 ? ?) -HL12 -HLK1 // /2 width=4/
| /4 width=1/
| /3 width=1/
]
qed.

lemma tps_refl: ∀T,L,d,e. L ⊢ T ▶ [d, e] T.
#T elim T -T //
#I elim I -I /2 width=1/
qed.

(* Basic_1: was: subst1_ex *)
lemma tps_full: ∀K,V,T1,L,d. ⇩[0, d] L ≡ (K. ⓓV) →
                ∃∃T2,T. L ⊢ T1 ▶ [d, 1] T2 & ⇧[d, 1] T ≡ T2.
#K #V #T1 elim T1 -T1
[ * #i #L #d #HLK /2 width=4/
  elim (lt_or_eq_or_gt i d) #Hid /3 width=4/
  destruct
  elim (lift_total V 0 (i+1)) #W #HVW
  elim (lift_split … HVW i i ? ? ?) // /3 width=4/
| * [ #a ] #I #W1 #U1 #IHW1 #IHU1 #L #d #HLK
  elim (IHW1 … HLK) -IHW1 #W2 #W #HW12 #HW2
  [ elim (IHU1 (L. ⓑ{I} W2) (d+1) ?) -IHU1 /2 width=1/ -HLK /3 width=9/
  | elim (IHU1 … HLK) -IHU1 -HLK /3 width=8/
  ]
]
qed.

lemma tps_weak: ∀L,T1,T2,d1,e1. L ⊢ T1 ▶ [d1, e1] T2 →
                ∀d2,e2. d2 ≤ d1 → d1 + e1 ≤ d2 + e2 →
                L ⊢ T1 ▶ [d2, e2] T2.
#L #T1 #T2 #d1 #e1 #H elim H -L -T1 -T2 -d1 -e1
[ //
| #L #K #V #W #i #d1 #e1 #Hid1 #Hide1 #HLK #HVW #d2 #e2 #Hd12 #Hde12
  lapply (transitive_le … Hd12 … Hid1) -Hd12 -Hid1 #Hid2
  lapply (lt_to_le_to_lt … Hide1 … Hde12) -Hide1 /2 width=4/
| /4 width=3/
| /4 width=1/
]
qed.

lemma tps_weak_top: ∀L,T1,T2,d,e.
                    L ⊢ T1 ▶ [d, e] T2 → L ⊢ T1 ▶ [d, |L| - d] T2.
#L #T1 #T2 #d #e #H elim H -L -T1 -T2 -d -e
[ //
| #L #K #V #W #i #d #e #Hdi #_ #HLK #HVW
  lapply (ldrop_fwd_ldrop2_length … HLK) #Hi
  lapply (le_to_lt_to_lt … Hdi Hi) /3 width=4/
| normalize /2 width=1/
| /2 width=1/
]
qed.

lemma tps_weak_full: ∀L,T1,T2,d,e.
                     L ⊢ T1 ▶ [d, e] T2 → L ⊢ T1 ▶ [0, |L|] T2.
#L #T1 #T2 #d #e #HT12
lapply (tps_weak … HT12 0 (d + e) ? ?) -HT12 // #HT12
lapply (tps_weak_top … HT12) //
qed.

lemma tps_split_up: ∀L,T1,T2,d,e. L ⊢ T1 ▶ [d, e] T2 → ∀i. d ≤ i → i ≤ d + e →
                    ∃∃T. L ⊢ T1 ▶ [d, i - d] T & L ⊢ T ▶ [i, d + e - i] T2.
#L #T1 #T2 #d #e #H elim H -L -T1 -T2 -d -e
[ /2 width=3/
| #L #K #V #W #i #d #e #Hdi #Hide #HLK #HVW #j #Hdj #Hjde
  elim (lt_or_ge i j)
  [ -Hide -Hjde
    >(plus_minus_m_m j d) in ⊢ (% → ?); // -Hdj /3 width=4/
  | -Hdi -Hdj #Hij
    lapply (plus_minus_m_m … Hjde) -Hjde /3 width=8/
  ]
| #L #a #I #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #i #Hdi #Hide
  elim (IHV12 i ? ?) -IHV12 // #V #HV1 #HV2
  elim (IHT12 (i + 1) ? ?) -IHT12 /2 width=1/
  -Hdi -Hide >arith_c1x #T #HT1 #HT2
  lapply (tps_lsubr_trans … HT1 (L. ⓑ{I} V) ?) -HT1 /3 width=5/
| #L #I #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #i #Hdi #Hide
  elim (IHV12 i ? ?) -IHV12 // elim (IHT12 i ? ?) -IHT12 //
  -Hdi -Hide /3 width=5/
]
qed.

lemma tps_split_down: ∀L,T1,T2,d,e. L ⊢ T1 ▶ [d, e] T2 →
                      ∀i. d ≤ i → i ≤ d + e →
                      ∃∃T. L ⊢ T1 ▶ [i, d + e - i] T &
                           L ⊢ T ▶ [d, i - d] T2.
#L #T1 #T2 #d #e #H elim H -L -T1 -T2 -d -e
[ /2 width=3/
| #L #K #V #W #i #d #e #Hdi #Hide #HLK #HVW #j #Hdj #Hjde
  elim (lt_or_ge i j)
  [ -Hide -Hjde >(plus_minus_m_m j d) in ⊢ (% → ?); // -Hdj /3 width=8/
  | -Hdi -Hdj
    >(plus_minus_m_m (d+e) j) in Hide; // -Hjde /3 width=4/
  ]
| #L #a #I #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #i #Hdi #Hide
  elim (IHV12 i ? ?) -IHV12 // #V #HV1 #HV2
  elim (IHT12 (i + 1) ? ?) -IHT12 /2 width=1/
  -Hdi -Hide >arith_c1x #T #HT1 #HT2
  lapply (tps_lsubr_trans … HT1 (L. ⓑ{I} V) ?) -HT1 /3 width=5/
| #L #I #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #i #Hdi #Hide
  elim (IHV12 i ? ?) -IHV12 // elim (IHT12 i ? ?) -IHT12 //
  -Hdi -Hide /3 width=5/
]
qed.

lemma tps_append: ∀K,T1,T2,d,e. K ⊢ T1 ▶ [d, e] T2 →
                  ∀L. L @@ K ⊢ T1 ▶ [d, e] T2.
#K #T1 #T2 #d #e #H elim H -K -T1 -T2 -d -e // /2 width=1/
#K #K0 #V #W #i #d #e #Hdi #Hide #HK0 #HVW #L
lapply (ldrop_fwd_ldrop2_length … HK0) #H
@(tps_subst … (L@@K0) … HVW) // (**) (* /3/ does not work *)
@(ldrop_O1_append_sn_le … HK0) /2 width=2/
qed.

(* Basic inversion lemmas ***************************************************)

fact tps_inv_atom1_aux: ∀L,T1,T2,d,e. L ⊢ T1 ▶ [d, e] T2 → ∀I. T1 = ⓪{I} →
                        T2 = ⓪{I} ∨
                        ∃∃K,V,i. d ≤ i & i < d + e &
                                 ⇩[O, i] L ≡ K. ⓓV &
                                 ⇧[O, i + 1] V ≡ T2 &
                                 I = LRef i.
#L #T1 #T2 #d #e * -L -T1 -T2 -d -e
[ #L #I #d #e #J #H destruct /2 width=1/
| #L #K #V #T2 #i #d #e #Hdi #Hide #HLK #HVT2 #I #H destruct /3 width=8/
| #L #a #I #V1 #V2 #T1 #T2 #d #e #_ #_ #J #H destruct
| #L #I #V1 #V2 #T1 #T2 #d #e #_ #_ #J #H destruct
]
qed.

lemma tps_inv_atom1: ∀L,T2,I,d,e. L ⊢ ⓪{I} ▶ [d, e] T2 →
                     T2 = ⓪{I} ∨
                     ∃∃K,V,i. d ≤ i & i < d + e &
                              ⇩[O, i] L ≡ K. ⓓV &
                              ⇧[O, i + 1] V ≡ T2 &
                              I = LRef i.
/2 width=3/ qed-.


(* Basic_1: was: subst1_gen_sort *)
lemma tps_inv_sort1: ∀L,T2,k,d,e. L ⊢ ⋆k ▶ [d, e] T2 → T2 = ⋆k.
#L #T2 #k #d #e #H
elim (tps_inv_atom1 … H) -H //
* #K #V #i #_ #_ #_ #_ #H destruct
qed-.

(* Basic_1: was: subst1_gen_lref *)
lemma tps_inv_lref1: ∀L,T2,i,d,e. L ⊢ #i ▶ [d, e] T2 →
                     T2 = #i ∨
                     ∃∃K,V. d ≤ i & i < d + e &
                            ⇩[O, i] L ≡ K. ⓓV &
                            ⇧[O, i + 1] V ≡ T2.
#L #T2 #i #d #e #H
elim (tps_inv_atom1 … H) -H /2 width=1/
* #K #V #j #Hdj #Hjde #HLK #HVT2 #H destruct /3 width=4/
qed-.

lemma tps_inv_gref1: ∀L,T2,p,d,e. L ⊢ §p ▶ [d, e] T2 → T2 = §p.
#L #T2 #p #d #e #H
elim (tps_inv_atom1 … H) -H //
* #K #V #i #_ #_ #_ #_ #H destruct
qed-.

fact tps_inv_bind1_aux: ∀d,e,L,U1,U2. L ⊢ U1 ▶ [d, e] U2 →
                        ∀a,I,V1,T1. U1 = ⓑ{a,I} V1. T1 →
                        ∃∃V2,T2. L ⊢ V1 ▶ [d, e] V2 &
                                 L. ⓑ{I} V2 ⊢ T1 ▶ [d + 1, e] T2 &
                                 U2 = ⓑ{a,I} V2. T2.
#d #e #L #U1 #U2 * -d -e -L -U1 -U2
[ #L #k #d #e #a #I #V1 #T1 #H destruct
| #L #K #V #W #i #d #e #_ #_ #_ #_ #a #I #V1 #T1 #H destruct
| #L #b #J #V1 #V2 #T1 #T2 #d #e #HV12 #HT12 #a #I #V #T #H destruct /2 width=5/
| #L #J #V1 #V2 #T1 #T2 #d #e #_ #_ #a #I #V #T #H destruct
]
qed.

lemma tps_inv_bind1: ∀d,e,L,a,I,V1,T1,U2. L ⊢ ⓑ{a,I} V1. T1 ▶ [d, e] U2 →
                     ∃∃V2,T2. L ⊢ V1 ▶ [d, e] V2 &
                              L. ⓑ{I} V2 ⊢ T1 ▶ [d + 1, e] T2 &
                              U2 = ⓑ{a,I} V2. T2.
/2 width=3/ qed-.

fact tps_inv_flat1_aux: ∀d,e,L,U1,U2. L ⊢ U1 ▶ [d, e] U2 →
                        ∀I,V1,T1. U1 = ⓕ{I} V1. T1 →
                        ∃∃V2,T2. L ⊢ V1 ▶ [d, e] V2 & L ⊢ T1 ▶ [d, e] T2 &
                                 U2 =  ⓕ{I} V2. T2.
#d #e #L #U1 #U2 * -d -e -L -U1 -U2
[ #L #k #d #e #I #V1 #T1 #H destruct
| #L #K #V #W #i #d #e #_ #_ #_ #_ #I #V1 #T1 #H destruct
| #L #a #J #V1 #V2 #T1 #T2 #d #e #_ #_ #I #V #T #H destruct
| #L #J #V1 #V2 #T1 #T2 #d #e #HV12 #HT12 #I #V #T #H destruct /2 width=5/
]
qed.

lemma tps_inv_flat1: ∀d,e,L,I,V1,T1,U2. L ⊢ ⓕ{I} V1. T1 ▶ [d, e] U2 →
                     ∃∃V2,T2. L ⊢ V1 ▶ [d, e] V2 & L ⊢ T1 ▶ [d, e] T2 &
                              U2 =  ⓕ{I} V2. T2.
/2 width=3/ qed-.

fact tps_inv_refl_O2_aux: ∀L,T1,T2,d,e. L ⊢ T1 ▶ [d, e] T2 → e = 0 → T1 = T2.
#L #T1 #T2 #d #e #H elim H -L -T1 -T2 -d -e
[ //
| #L #K #V #W #i #d #e #Hdi #Hide #_ #_ #H destruct
  lapply (le_to_lt_to_lt … Hdi … Hide) -Hdi -Hide <plus_n_O #Hdd
  elim (lt_refl_false … Hdd)
| /3 width=1/
| /3 width=1/
]
qed.

lemma tps_inv_refl_O2: ∀L,T1,T2,d. L ⊢ T1 ▶ [d, 0] T2 → T1 = T2.
/2 width=6/ qed-.

(* Basic forward lemmas *****************************************************)

lemma tps_fwd_tw: ∀L,T1,T2,d,e. L ⊢ T1 ▶ [d, e] T2 → ♯{T1} ≤ ♯{T2}.
#L #T1 #T2 #d #e #H elim H -L -T1 -T2 -d -e normalize
/3 by monotonic_le_plus_l, le_plus/ (**) (* just /3 width=1/ is too slow *)
qed-.

lemma tps_fwd_shift1: ∀L1,L,T1,T,d,e. L ⊢ L1 @@ T1 ▶[d, e] T →
                      ∃∃L2,T2. |L1| = |L2| & T = L2 @@ T2.
#L1 @(lenv_ind_dx … L1) -L1 normalize
[ #L #T1 #T #d #e #HT1
  @(ex2_2_intro … (⋆)) // (**) (* explicit constructor *)
| #I #L1 #V1 #IH #L #T1 #X #d #e
  >shift_append_assoc normalize #H
  elim (tps_inv_bind1 … H) -H
  #V0 #T0 #_ #HT10 #H destruct
  elim (IH … HT10) -IH -HT10 #L2 #T2 #HL12 #H destruct
  >append_length >HL12 -HL12
  @(ex2_2_intro … (⋆.ⓑ{I}V0@@L2) T2) [ >append_length ] // /2 width=3/ (**) (* explicit constructor *)
]
qed-.

(* Basic_1: removed theorems 25:
            subst0_gen_sort subst0_gen_lref subst0_gen_head subst0_gen_lift_lt
            subst0_gen_lift_false subst0_gen_lift_ge subst0_refl subst0_trans
            subst0_lift_lt subst0_lift_ge subst0_lift_ge_S subst0_lift_ge_s
            subst0_subst0 subst0_subst0_back subst0_weight_le subst0_weight_lt
            subst0_confluence_neq subst0_confluence_eq subst0_tlt_head
            subst0_confluence_lift subst0_tlt
            subst1_head subst1_gen_head subst1_lift_S subst1_confluence_lift
*)
