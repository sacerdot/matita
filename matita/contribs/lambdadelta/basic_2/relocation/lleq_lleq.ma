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

include "basic_2/relocation/ldrop_ldrop.ma".
include "basic_2/relocation/lleq.ma".

(* LAZY EQUIVALENCE FOR LOCAL ENVIRONMENTS **********************************)

(* Advanced inversion lemmas ************************************************)

lemma lleq_inv_lref_dx: ∀L1,L2,d,i. L1 ⋕[d, #i] L2 →
                        ∀I,K2,V. ⇩[0, i] L2 ≡ K2.ⓑ{I}V →
                        (∃∃K1. ⇩[0, i] L1 ≡ K1.ⓑ{I}V & K1 ⋕[0, V] K2 & d ≤ i) ∨
                        ∃∃I1,K1,V1. ⇩[0, i] L1 ≡ K1.ⓑ{I1}V1 &
                                    K1 ⋕[d-i-1, V1] K2 & K1 ⋕[d-i-1, V] K2 &
                                    i < d.
#L1 #L2 #d #i #H #I #K2 #V #HLK2 elim (lleq_inv_lref … H) -H *
[ #_ #H elim (lt_refl_false i)
  lapply (ldrop_fwd_length_lt2 … HLK2) -HLK2
  /2 width=3 by lt_to_le_to_lt/ (**) (* full auto too slow *)
| #I1 #I2 #K11 #K22 #V1 #V2 #HLK11 #HLK22 #HV1 #HV2 #Hdi lapply (ldrop_mono … HLK22 … HLK2) -L2
  #H destruct /3 width=6 by ex4_3_intro, or_intror/
| #I0 #K1 #K0 #V0 #HLK1 #HLK0 #HK10 #Hdi lapply (ldrop_mono … HLK0 … HLK2) -L2
  #H destruct /3 width=3 by ex3_intro, or_introl/
]
qed-.

lemma lleq_inv_lref_sn: ∀L1,L2,d,i. L1 ⋕[d, #i] L2 →
                        ∀I,K1,V. ⇩[0, i] L1 ≡ K1.ⓑ{I}V →
                        (∃∃K2. ⇩[0, i] L2 ≡ K2.ⓑ{I}V & K1 ⋕[0, V] K2 & d ≤ i) ∨
                        ∃∃I2,K2,V2. ⇩[0, i] L2 ≡ K2.ⓑ{I2}V2 &
                                    K1 ⋕[d-i-1, V] K2 & K1 ⋕[d-i-1, V2] K2 &
                                    i < d.
#L1 #L2 #d #i #HL12 #I #K1 #V #HLK1 elim (lleq_inv_lref_dx L2 … d … HLK1) -HLK1
[1,2: * ] /4 width=6 by lleq_sym, ex4_3_intro, ex3_intro, or_introl, or_intror/
qed-.

lemma lleq_inv_lref_ge_dx: ∀L1,L2,d,i. L1 ⋕[d, #i] L2 → d ≤ i →
                           ∀I,K2,V. ⇩[0, i] L2 ≡ K2.ⓑ{I}V →
                           ∃∃K1. ⇩[0, i] L1 ≡ K1.ⓑ{I}V & K1 ⋕[0, V] K2.
#L1 #L2 #d #i #H #Hdi #I #K2 #V #HLK2 elim (lleq_inv_lref … H) -H *
[ #_ #H elim (lt_refl_false i)
  lapply (ldrop_fwd_length_lt2 … HLK2) -HLK2
  /2 width=3 by lt_to_le_to_lt/ (**) (* full auto too slow *)
| -HLK2 #I1 #I2 #K11 #K22 #V1 #V2 #_ #_ #_ #_ #H elim (lt_refl_false i)
  /2 width=3 by lt_to_le_to_lt/
| #I0 #K1 #K0 #V0 #HLK1 #HLK0 #HK10 #_ lapply (ldrop_mono … HLK0 … HLK2) -L2
  #H destruct /2 width=3 by ex2_intro/
]
qed-.

lemma lleq_inv_lref_ge_sn: ∀L1,L2,d,i. L1 ⋕[d, #i] L2 → d ≤ i →
                           ∀I,K1,V. ⇩[0, i] L1 ≡ K1.ⓑ{I}V →
                           ∃∃K2. ⇩[0, i] L2 ≡ K2.ⓑ{I}V & K1 ⋕[0, V] K2.
#L1 #L2 #d #i #HL12 #Hdi #I #K1 #V #HLK1 elim (lleq_inv_lref_ge_dx L2 … Hdi … HLK1) -Hdi -HLK1
/3 width=3 by lleq_sym, ex2_intro/
qed-.

fact lleq_inv_S_aux: ∀L1,L2,T,d0. L1 ⋕[d0, T] L2 → ∀d. d0 = d + 1 →
                     ∀K1,K2,I,V. ⇩[0, d] L1 ≡ K1.ⓑ{I}V → ⇩[0, d] L2 ≡ K2.ⓑ{I}V →
                     L1 ⋕[d, T] L2.
#L1 #L2 #T #d0 #H elim H -L1 -L2 -T -d0
/2 width=1 by lleq_sort, lleq_free, lleq_gref/
[ #I1 #I2 #L1 #L2 #K11 #K22 #V1 #V2 #d0 #i #Hid0 #HLK11 #HLK22 #HV1 #_ #IHV1 #IHV2 #d #H #K1 #K2 #J #W #HLK1 #HLK2 destruct
  elim (le_to_or_lt_eq i d) /2 width=1 by lleq_skip, monotonic_pred/ -Hid0 
  [ -HV1 #Hid
    lapply (ldrop_fwd_ldrop2 … HLK11) #H1
    lapply (ldrop_fwd_ldrop2 … HLK22) #H2
    lapply (ldrop_conf_ge … H1 … HLK1 ?) // -H1 -HLK1
    lapply (ldrop_conf_ge … H2 … HLK2 ?) // -H2 -HLK2
    <minus_plus /4 width=10 by lleq_skip, arith_i/
  | -IHV1 -IHV2 #H destruct
    lapply (ldrop_mono … HLK11 … HLK1) -HLK11 #H destruct
    lapply (ldrop_mono … HLK22 … HLK2) -HLK22 #H destruct
    /2 width=7 by lleq_lref/
  ]
| #I #L1 #L2 #K11 #K22 #V #d0 #i #Hid0 #HLK11 #HLK22 #HV #_ #d #H #K1 #K2 #J #W #HLK1 #HLK2 destruct
  /3 width=7 by lleq_lref, lt_to_le/
| #a #I #L1 #L2 #V #T #d0 #_ #_ #IHV #IHT #d #H #K1 #K2 #J #W #HLK1 #HLK2 destruct
  /4 width=6 by lleq_bind, ldrop_ldrop/
| #I #L1 #L2 #V #T #d0 #_ #_ #IHV #IHT #d #H #K1 #K2 #J #W #HLK1 #HLK2 destruct
  /3 width=6 by lleq_flat/
]
qed-.

lemma lleq_inv_S: ∀T,L1,L2,d. L1 ⋕[d+1, T] L2 →
                  ∀K1,K2,I,V. ⇩[0, d] L1 ≡ K1.ⓑ{I}V → ⇩[0, d] L2 ≡ K2.ⓑ{I}V →
                  L1 ⋕[d, T] L2.
/2 width=6 by lleq_inv_S_aux/ qed-.

lemma lleq_inv_bind_O: ∀a,I,L1,L2,V,T. L1 ⋕[0, ⓑ{a,I}V.T] L2 →
                       L1 ⋕[0, V] L2 ∧ L1.ⓑ{I}V ⋕[0, T] L2.ⓑ{I}V.
#a #I #L1 #L2 #V #T #H elim (lleq_inv_bind … H) -H
/3 width=6 by ldrop_pair, conj, lleq_inv_S/
qed-.

lemma lleq_inv_lift_le: ∀L1,L2,U,d0. L1 ⋕[d0, U] L2 →
                        ∀K1,K2,d,e. ⇩[d, e] L1 ≡ K1 → ⇩[d, e] L2 ≡ K2 →
                        ∀T. ⇧[d, e] T ≡ U → d0 ≤ d → K1 ⋕[d0, T] K2.
#L1 #L2 #U #d0 #H elim H -L1 -L2 -U -d0
[ #L1 #L2 #d0 #k #HL12 #K1 #K2 #d #e #HLK1 #HLK2 #X #H #_ >(lift_inv_sort2 … H) -X
  lapply (ldrop_fwd_length_eq1 … HLK1 HLK2 HL12) -L1 -L2 -d -e
  /2 width=1 by lleq_sort/
| #I1 #I2 #L1 #L2 #K11 #K22 #W1 #W2 #d0 #i #Hid0 #HLK11 #HLK22 #HW1 #HW2 #IHW1 #IHW2 #K1 #K2 #d #e #HLK1 #HLK2 #X #H #Hd0 elim (lift_inv_lref2 … H) -H
  * #Hid #H destruct [ -HW1 -HW2 | -IHW1 -IHW2 ]
  [ elim (ldrop_conf_lt … HLK1 … HLK11) // -L1
    elim (ldrop_conf_lt … HLK2 … HLK22) // -Hid -L2
    #L2 #V2 #HKL2 #HKL22 #HVW2 #L1 #V1 #HKL1 #HKL11 #HVW1
    @(lleq_skip … HKL1 HKL2) -HKL1 -HKL2 /3 width=6 by monotonic_le_minus_l2/ (**) (* full auto fails *)
  | lapply (ldrop_conf_ge … HLK1 … HLK11 ?) // -L1
    lapply (ldrop_conf_ge … HLK2 … HLK22 ?) // -Hid -L2
    #HK22 #HK11 @(lleq_skip … HK11 HK22) -HK11 -HK22
    /2 width=3 by lleq_ge, le_to_lt_to_lt/ (**) (* full auto fails *)
  ]
| #I #L1 #L2 #K11 #K22 #W #d0 #i #Hid0 #HLK11 #HLK22 #HW #IHW #K1 #K2 #d #e #HLK1 #HLK2 #X #H #Hd0 elim (lift_inv_lref2 … H) -H
  * #Hid #H destruct [ -HW | -IHW ]
  [ elim (ldrop_conf_lt … HLK1 … HLK11) // -L1 #L1 #V #HKL1 #KL11 #HVW
    elim (ldrop_conf_lt … HLK2 … HLK22) // -Hid -L2 #L2 #V0 #HKL2 #KL22 #HV0
    lapply (lift_inj … HV0 … HVW) -HV0 #H destruct /3 width=12 by lleq_lref/
  | lapply (ldrop_conf_ge … HLK1 … HLK11 ?) // -L1
    lapply (ldrop_conf_ge … HLK2 … HLK22 ?) // -L2 -Hid0
    elim (le_inv_plus_l … Hid) -Hid /3 width=7 by lleq_lref, transitive_le/
  ]
| #L1 #L2 #d0 #i #HL1 #HL2 #HL12 #K1 #K2 #d #e #HLK1 #HLK2 #X #H #Hd0 elim (lift_inv_lref2 … H) -H
  * #_ #H destruct
  lapply (ldrop_fwd_length_eq1 … HLK1 HLK2 HL12)
  [ lapply (ldrop_fwd_length_le4 … HLK1) -HLK1
    lapply (ldrop_fwd_length_le4 … HLK2) -HLK2
    #HKL2 #HKL1 #HK12 @lleq_free // /2 width=3 by transitive_le/ (**) (* full auto too slow *)
  | lapply (ldrop_fwd_length … HLK1) -HLK1 #H >H in HL1; -H
    lapply (ldrop_fwd_length … HLK2) -HLK2 #H >H in HL2; -H
    /3 width=1 by lleq_free, le_plus_to_minus_r/
  ]
| #L1 #L2 #d0 #p #HL12 #K1 #K2 #d #e #HLK1 #HLK2 #X #H #_ >(lift_inv_gref2 … H) -X
  lapply (ldrop_fwd_length_eq1 … HLK1 HLK2 HL12) -L1 -L2 -d -e
  /2 width=1 by lleq_gref/
| #a #I #L1 #L2 #W #U #d0 #_ #_ #IHW #IHU #K1 #K2 #d #e #HLK1 #HLK2 #X #H #Hd0 elim (lift_inv_bind2 … H) -H
  #V #T #HVW #HTU #H destruct /4 width=6 by lleq_bind, ldrop_skip, le_S_S/
| #I #L1 #L2 #W #U #d0 #_ #_ #IHW #IHU #K1 #K2 #d #e #HLK1 #HLK2 #X #H #Hd0 elim (lift_inv_flat2 … H) -H
  #V #T #HVW #HTU #H destruct /3 width=6 by lleq_flat/
]
qed-.

lemma lleq_inv_lift_ge: ∀L1,L2,U,d0. L1 ⋕[d0, U] L2 →
                        ∀K1,K2,d,e. ⇩[d, e] L1 ≡ K1 → ⇩[d, e] L2 ≡ K2 →
                        ∀T. ⇧[d, e] T ≡ U → d+e ≤ d0 → K1 ⋕[d0-e, T] K2.
#L1 #L2 #U #d0 #H elim H -L1 -L2 -U -d0
[ #L1 #L2 #d0 #k #HL12 #K1 #K2 #d #e #HLK1 #HLK2 #X #H #_ >(lift_inv_sort2 … H) -X
  lapply (ldrop_fwd_length_eq1 … HLK1 HLK2 HL12) -L1 -L2 -d
  /2 width=1 by lleq_sort/
| #I1 #I2 #L1 #L2 #K11 #K22 #W1 #W2 #d0 #i #Hid0 #HLK11 #HLK22 #HW1 #HW2 #IHW1 #IHW2 #K1 #K2 #d #e #HLK1 #HLK2 #X #H #Hded0 elim (lift_inv_lref2 … H) -H
  * #Hid #H destruct [ -HW1 -HW2 | -IHW1 -IHW2 ]
  [ elim (ldrop_conf_lt … HLK1 … HLK11) // -L1
    elim (ldrop_conf_lt … HLK2 … HLK22) // -L2
    elim (le_inv_plus_l … Hded0) #Hdd0e #_
    #L2 #V2 #HKL2 #HKL22 #HVW2 #L1 #V1 #HKL1 #HKL11 #HVW1
    @(lleq_skip … HKL1 HKL2) -HKL1 -HKL2 [ /2 width=3 by lt_to_le_to_lt/ ] (**) (* explicit constructor *)
    >minus_minus_comm3 /3 width=6 by arith_k_sn/ (**) (* slow *)
  | lapply (ldrop_conf_ge … HLK1 … HLK11 ?) // -L1
    lapply (ldrop_conf_ge … HLK2 … HLK22 ?) // -L2 -Hded0
    elim (le_inv_plus_l … Hid) -Hid #_ #Hei
    #HK22 #HK11 @(lleq_skip … HK11 HK22) -HK11 -HK22 (**) (* explicit constructor *)
    [ /2 width=1 by monotonic_lt_minus_l/ ] >arith_b1 //
  ]
| #I #L1 #L2 #K11 #K22 #W #d0 #i #Hid0 #HLK11 #HLK22 #HW #_ #K1 #K2 #d #e #HLK1 #HLK2 #X #H #Hded0 elim (lift_inv_lref2 … H) -H
  * #Hid #H destruct
  [ -I -L1 -L2 -K11 -K22 -W elim (le_plus_xySz_x_false e 0 d)
    /3 width=3 by transitive_le, le_to_lt_to_lt/
  | lapply (ldrop_conf_ge … HLK1 … HLK11 ?) // -L1
    lapply (ldrop_conf_ge … HLK2 … HLK22 ?) // -L2 -Hded0
    /3 width=7 by lleq_lref, monotonic_le_minus_l/
  ]
| #L1 #L2 #d0 #i #HL1 #HL2 #HL12 #K1 #K2 #d #e #HLK1 #HLK2 #X #H #Hded0 elim (lift_inv_lref2 … H) -H
  * #_ #H destruct
  lapply (ldrop_fwd_length_eq1 … HLK1 HLK2 HL12)
  [ lapply (ldrop_fwd_length_le4 … HLK1) -HLK1
    lapply (ldrop_fwd_length_le4 … HLK2) -HLK2
    #HKL2 #HKL1 #HK12 @lleq_free // /2 width=3 by transitive_le/ (**) (* full auto too slow *)
  | lapply (ldrop_fwd_length … HLK1) -HLK1 #H >H in HL1; -H
    lapply (ldrop_fwd_length … HLK2) -HLK2 #H >H in HL2; -H
    /3 width=1 by lleq_free, le_plus_to_minus_r/
  ]
| #L1 #L2 #d0 #p #HL12 #K1 #K2 #d #e #HLK1 #HLK2 #X #H #_ >(lift_inv_gref2 … H) -X
  lapply (ldrop_fwd_length_eq1 … HLK1 HLK2 HL12) -L1 -L2 -d
  /2 width=1 by lleq_gref/
| #a #I #L1 #L2 #W #U #d0 #_ #_ #IHW #IHU #K1 #K2 #d #e #HLK1 #HLK2 #X #H #Hded0 elim (lift_inv_bind2 … H) -H
  #V #T #HVW #HTU #H destruct
  elim (le_inv_plus_l … Hded0) #_ #Hed0
  @lleq_bind [ /2 width=5 by/ ] -IHW (**) (* explicit constructor *)
  >plus_minus /3 width=5 by ldrop_skip, le_minus_to_plus/
| #I #L1 #L2 #W #U #d0 #_ #_ #IHW #IHU #K1 #K2 #d #e #HLK1 #HLK2 #X #H #Hded0 elim (lift_inv_flat2 … H) -H
  #V #T #HVW #HTU #H destruct /3 width=5 by lleq_flat/
]
qed-.

lemma lleq_inv_lift_be: ∀L1,L2,U,d0. L1 ⋕[d0, U] L2 →
                        ∀K1,K2,d,e. ⇩[d, e] L1 ≡ K1 → ⇩[d, e] L2 ≡ K2 →
                        ∀T. ⇧[d, e] T ≡ U → d ≤ d0 → d0 ≤ d + e → K1 ⋕[d, T] K2.
#L1 #L2 #U #d0 #H elim H -L1 -L2 -U -d0
[ #L1 #L2 #d0 #k #HL12 #K1 #K2 #d #e #HLK1 #HLK2 #X #H #_ #_ >(lift_inv_sort2 … H) -X
  lapply (ldrop_fwd_length_eq1 … HLK1 HLK2 HL12) -L1 -L2 -d0 -e
  /2 width=1 by lleq_sort/
| #I1 #I2 #L1 #L2 #K11 #K22 #W1 #W2 #d0 #i #Hid0 #HLK11 #HLK22 #_ #_ #IHW1 #IHW2 #K1 #K2 #d #e #HLK1 #HLK2 #X #H #Hd0 #Hde elim (lift_inv_lref2 … H) -H
  * #Hid #H destruct
  [ elim (ldrop_conf_lt … HLK1 … HLK11) // -L1
    elim (ldrop_conf_lt … HLK2 … HLK22) // -L2 -Hid0
    #L2 #V2 #HKL2 #HKL22 #HVW2 #L1 #V1 #HKL1 #HKL11 #HVW1
    @(lleq_skip … HKL1 HKL2) -HKL1 -HKL2 //
    /3 width=6 by arith_k_dx, monotonic_le_minus_l2/ (**) (* full auto fails *)
  | -I1 -I2 -L1 -L2 -K11 -K22 -W1 -W2 -Hd0 elim (lt_refl_false i)
    /3 width=3 by lt_to_le_to_lt, transitive_le/ (**) (* slow *) 
  ]
| #I #L1 #L2 #K11 #K22 #W #d0 #i #Hid0 #HLK11 #HLK22 #HW #_ #K1 #K2 #d #e #HLK1 #HLK2 #X #H #Hd0 #Hde elim (lift_inv_lref2 … H) -H
  * #Hid #H destruct
  [ -I -L1 -L2 -K11 -K22 -W -Hde elim (lt_refl_false i)
    /3 width=3 by lt_to_le_to_lt, transitive_le/ (**) (* slow *)
  | lapply (ldrop_conf_ge … HLK1 … HLK11 ?) // -L1
    lapply (ldrop_conf_ge … HLK2 … HLK22 ?) // -L2 -Hid0 -Hd0 -Hde
    elim (le_inv_plus_l … Hid) -Hid /2 width=7 by lleq_lref/
  ]
| #L1 #L2 #d0 #i #HL1 #HL2 #HL12 #K1 #K2 #d #e #HLK1 #HLK2 #X #H #Hd0 #Hde elim (lift_inv_lref2 … H) -H
  * #_ #H destruct
  lapply (ldrop_fwd_length_eq1 … HLK1 HLK2 HL12)
  [ lapply (ldrop_fwd_length_le4 … HLK1) -HLK1
    lapply (ldrop_fwd_length_le4 … HLK2) -HLK2
    #HKL2 #HKL1 #HK12 @lleq_free // /2 width=3 by transitive_le/ (**) (* full auto too slow *)
  | lapply (ldrop_fwd_length … HLK1) -HLK1 #H >H in HL1; -H
    lapply (ldrop_fwd_length … HLK2) -HLK2 #H >H in HL2; -H
    /3 width=1 by lleq_free, le_plus_to_minus_r/
  ]
| #L1 #L2 #d0 #p #HL12 #K1 #K2 #d #e #HLK1 #HLK2 #X #H #_ #_ >(lift_inv_gref2 … H) -X
  lapply (ldrop_fwd_length_eq1 … HLK1 HLK2 HL12) -L1 -L2 -d0 -e
  /2 width=1 by lleq_gref/
| #a #I #L1 #L2 #W #U #d0 #_ #_ #IHW #IHU #K1 #K2 #d #e #HLK1 #HLK2 #X #H #Hd0 #Hde elim (lift_inv_bind2 … H) -H
  #V #T #HVW #HTU #H destruct
  @lleq_bind [ /2 width=5 by/ ] -IHW
  @(IHU … HTU) -IHU -HTU /2 width=1 by ldrop_skip, le_S_S/ (**) (* full auto too slow *)
| #I #L1 #L2 #W #U #d0 #_ #_ #IHW #IHU #K1 #K2 #d #e #HLK1 #HLK2 #X #H #Hd0 #Hde elim (lift_inv_flat2 … H) -H
  #V #T #HVW #HTU #H destruct /3 width=6 by lleq_flat/
]
qed-.

(* Advanced properties ******************************************************)

lemma lleq_lift_le: ∀K1,K2,T,d0. K1 ⋕[d0, T] K2 →
                    ∀L1,L2,d,e. ⇩[d, e] L1 ≡ K1 → ⇩[d, e] L2 ≡ K2 →
                    ∀U. ⇧[d, e] T ≡ U → d0 ≤ d → L1 ⋕[d0, U] L2.
#K1 #K2 #T #d0 #H elim H -K1 -K2 -T -d0
[ #K1 #K2 #d0 #k #HK12 #L1 #L2 #d #e #HLK1 #HLK2 #X #H #_ >(lift_inv_sort1 … H) -X
  lapply (ldrop_fwd_length_eq2 … HLK1 HLK2 HK12) -K1 -K2 -d
  /2 width=1 by lleq_sort/
| #I1 #I2 #K1 #K2 #K11 #K22 #V1 #V2 #d0 #i #Hid0 #HK11 #HK22 #_ #_ #IHV1 #IHV2 #L1 #L2 #d #e #HLK1 #HLK2 #X #H #Hd0 elim (lift_inv_lref1 … H) -H
  * #Hdi #H destruct
  [ elim (ldrop_trans_lt … HLK1 … HK11) // -K1
    elim (ldrop_trans_lt … HLK2 … HK22) // -K2
    #K2 #W2 #HLK2 #HK22 #HVW2 #K1 #W1 #HLK1 #HK11 #HVW1 -Hdi
    @(lleq_skip … HLK1 HLK2) // /3 width=6 by monotonic_le_minus_l2/ (**) (* full auto fails *)
  | elim (lt_refl_false i) -I1 -I2 -L1 -L2 -K1 -K2 -K11 -K22 -V1 -V2 -e
    /3 width=3 by lt_to_le_to_lt, transitive_le/ (**) (* slow *)
  ]
| #I #K1 #K2 #K11 #K22 #V #d0 #i #Hid0 #HK11 #HK22 #HV #IHV #L1 #L2 #d #e #HLK1 #HLK2 #X #H #Hd0 elim (lift_inv_lref1 … H) -H
  * #Hdi #H destruct [ -HV | -IHV ]
  [ elim (ldrop_trans_lt … HLK1 … HK11) // -K1 #K1 #W #HLK1 #HK11 #HVW
    elim (ldrop_trans_lt … HLK2 … HK22) // -Hdi -K2 #K2 #W2 #HLK2 #HK22 #HVW2
    lapply (lift_mono … HVW2 … HVW) -HVW2 #H destruct /3 width=12 by lleq_lref/
  | lapply (ldrop_trans_ge … HLK1 … HK11 ?) // -K1
    lapply (ldrop_trans_ge … HLK2 … HK22 ?) // -Hdi -K2
    /3 width=7 by lleq_lref, transitive_le/
  ]
| #K1 #K2 #d0 #i #HK1 #HK2 #HK12 #L1 #L2 #d #e #HLK1 #HLK2 #X #H #Hd0 elim (lift_inv_lref1 … H) -H
  * #Hid #H destruct
  lapply (ldrop_fwd_length_eq2 … HLK1 HLK2 HK12) -HK12
  [ /3 width=6 by lleq_free, ldrop_fwd_be/
  | lapply (ldrop_fwd_length … HLK1) -HLK1 #HLK1
    lapply (ldrop_fwd_length … HLK2) -HLK2 #HLK2
    @lleq_free [ >HLK1 | >HLK2 ] -Hid -HLK1 -HLK2 /2 width=1 by monotonic_le_plus_r/ (**) (* explicit constructor *)
  ]
| #K1 #K2 #d0 #p #HK12 #L1 #L2 #d #e #HLK1 #HLK2 #X #H #_ >(lift_inv_gref1 … H) -X
  lapply (ldrop_fwd_length_eq2 … HLK1 HLK2 HK12) -K1 -K2 -d -e
  /2 width=1 by lleq_gref/
| #a #I #K1 #K2 #V #T #d0 #_ #_ #IHV #IHT #L1 #L2 #d #e #HLK1 #HLK2 #X #H #Hd0 elim (lift_inv_bind1 … H) -H
  #W #U #HVW #HTU #H destruct /4 width=6 by lleq_bind, ldrop_skip, le_S_S/
| #I #K1 #K2 #V #T #d0 #_ #_ #IHV #IHT #L1 #L2 #d #e #HLK1 #HLK2 #X #H #Hd0 elim (lift_inv_flat1 … H) -H
  #W #U #HVW #HTU #H destruct /3 width=6 by lleq_flat/
]
qed-.

lemma lleq_lift_ge: ∀K1,K2,T,d0. K1 ⋕[d0, T] K2 →
                    ∀L1,L2,d,e. ⇩[d, e] L1 ≡ K1 → ⇩[d, e] L2 ≡ K2 →
                    ∀U. ⇧[d, e] T ≡ U → d ≤ d0 → L1 ⋕[d0+e, U] L2.
#K1 #K2 #T #d0 #H elim H -K1 -K2 -T -d0
[ #K1 #K2 #d0 #k #HK12 #L1 #L2 #d #e #HLK1 #HLK2 #X #H #_ >(lift_inv_sort1 … H) -X
  lapply (ldrop_fwd_length_eq2 … HLK1 HLK2 HK12) -K1 -K2 -d
  /2 width=1 by lleq_sort/
| #I1 #I2 #K1 #K2 #K11 #K22 #V1 #V2 #d0 #i #hid0 #HK11 #HK22 #HV1 #HV2 #IHV1 #IHV2 #L1 #L2 #d #e #HLK1 #HLK2 #X #H #Hd0 elim (lift_inv_lref1 … H) -H
  * #Hdi #H destruct [ -HV1 -HV2 | -IHV1 -IHV2 ]
  [ elim (ldrop_trans_lt … HLK1 … HK11) // -K1 #K1 #W1 #HLK1 #HK11 #HVW1
    elim (ldrop_trans_lt … HLK2 … HK22) // -K2 #K2 #W2 #HLK2 #HK22 #HVW2
    @(lleq_skip … HLK1 HLK2) -HLK1 -HLK2 (**) (* explicit constructor *)
    [ /2 width=3 by lt_to_le_to_lt/ ]
    >arith_i /3 width=5 by monotonic_le_minus_l2/
  | lapply (ldrop_trans_ge_comm … HLK1 … HK11 ?) // -K1
    lapply (ldrop_trans_ge_comm … HLK2 … HK22 ?) // -K2
    /4 width=10 by lleq_skip, monotonic_lt_plus_l/
  ]
| #I #K1 #K2 #K11 #K22 #V #d0 #i #Hid0 #HK11 #HK22 #HV #_ #L1 #L2 #d #e #HLK1 #HLK2 #X #H #Hd0 elim (lift_inv_lref1 … H) -H
  * #Hid #H destruct
  [ elim (lt_refl_false i) -I -L1 -L2 -K1 -K2 -K11 -K22 -V -e
    /3 width=3 by lt_to_le_to_lt, transitive_le/ (**) (* slow *)
  | lapply (ldrop_trans_ge … HLK1 … HK11 ?) // -K1
    lapply (ldrop_trans_ge … HLK2 … HK22 ?) // -Hid -K2
    /3 width=7 by lleq_lref, monotonic_le_plus_l/
  ]
| #K1 #K2 #d0 #i #HK1 #HK2 #HK12 #L1 #L2 #d #e #HLK1 #HLK2 #X #H #Hd0 elim (lift_inv_lref1 … H) -H
  * #Hid #H destruct
  lapply (ldrop_fwd_length_eq2 … HLK1 HLK2 HK12) -HK12
  [ /3 width=6 by lleq_free, ldrop_fwd_be/
  | lapply (ldrop_fwd_length … HLK1) -HLK1 #HLK1
    lapply (ldrop_fwd_length … HLK2) -HLK2 #HLK2
    @lleq_free [ >HLK1 | >HLK2 ] -Hid -HLK1 -HLK2 /2 width=1 by monotonic_le_plus_r/ (**) (* explicit constructor *)
  ]
| #K1 #K2 #d0 #p #HK12 #L1 #L2 #d #e #HLK1 #HLK2 #X #H #_ >(lift_inv_gref1 … H) -X
  lapply (ldrop_fwd_length_eq2 … HLK1 HLK2 HK12) -K1 -K2 -d
  /2 width=1 by lleq_gref/
| #a #I #K1 #K2 #V #T #d0 #_ #_ #IHV #IHT #L1 #L2 #d #e #HLK1 #HLK2 #X #H #Hd0 elim (lift_inv_bind1 … H) -H
  #W #U #HVW #HTU #H destruct /4 width=5 by lleq_bind, ldrop_skip, le_minus_to_plus/
| #I #K1 #K2 #V #T #d0 #_ #_ #IHV #IHT #L1 #L2 #d #e #HLK1 #HLK2 #X #H #Hd0 elim (lift_inv_flat1 … H) -H
  #W #U #HVW #HTU #H destruct /3 width=5 by lleq_flat/
]
qed-.

lemma lleq_be: ∀L1,L2,U,d0. L1 ⋕[d0, U] L2 →
               ∀K1,K2,d,e. ⇩[d, e] L1 ≡ K1 → ⇩[d, e] L2 ≡ K2 →
               ∀T. ⇧[d, e] T ≡ U → d ≤ d0 → d0 ≤ d + e → L1 ⋕[d, U] L2.
#L1 #L2 #U #d0 #H elim H -L1 -L2 -U -d0
/2 width=1 by lleq_sort, lleq_free, lleq_gref/
[ #I1 #I2 #L1 #L2 #K11 #K22 #W1 #W2 #d0 #i #Hid0 #HLK11 #HLK22 #_ #_ #IHW1 #IHW2 #K1 #K2 #d #e #HLK1 #HLK2 #X #H #Hd0 #Hd0de elim (lift_inv_lref2 … H) -H
  * #Hid #H destruct [ -Hid0 | -Hd0 ]
  [ elim (ldrop_conf_lt … HLK1 … HLK11) // -HLK1
    elim (ldrop_conf_lt … HLK2 … HLK22) // -HLK2
    #L2 #V2 #_ #HKL22 #HVW2 #L1 #V1 #_ #HKL21 #HVW1
    @(lleq_skip … HLK11 HLK22) -HLK11 -HLK22 //
    /3 width=8 by arith_k_dx, monotonic_le_minus_l2/ (**) (* full auto fails *)
  | -I1 -I2 -K11 -K22 -K1 -K2 -W1 -W2 elim (lt_refl_false … i) -L1 -L2
    @(lt_to_le_to_lt … Hid0) -Hid0 /2 width=3 by transitive_le/ (**) (* full auto too slow *)
  ]
| #I #L1 #L2 #K11 #K22 #W #d0 #i #Hid0 #HLK11 #HLK22 #HW #_ #K1 #K2 #d #e #_ #_ #X #H #Hd0 #_ elim (lift_inv_lref2 … H) -H
  * #Hid #H destruct
  [ -I -K1 -K2 -K11 -K22 -W elim (lt_refl_false i)
    @(lt_to_le_to_lt … Hid) -Hid /2 width=3 by transitive_le/ (**) (* full auto too slow *)
  | -d0 /3 width=7 by lleq_lref, le_plus_b/
  ]
| #a #I #L1 #L2 #W #U #d0 #_ #_ #IHW #IHU #K1 #K2 #d #e #HLK1 #HLK2 #X #H #Hd0 #Hde elim (lift_inv_bind2 … H) -H
  #V #T #HVW #HTU #H destruct
  @lleq_bind [ /2 width=8 by/ ] -IHW
  @(IHU … HTU) -IHU -HTU /2 width=2 by ldrop_skip, le_S_S/ (**) (* full auto too slow *)
| #I #L1 #L2 #W #U #d0 #_ #_ #IHW #IHU #K1 #K2 #d #e #HLK1 #HLK2 #X #H #Hd0 #Hde elim (lift_inv_flat2 … H) -H
  #V #T #HVW #HTU #H destruct /3 width=8 by lleq_flat/
]
qed-.

axiom- lleq_dec: ∀T,L1,L2,d. Decidable (L1 ⋕[d, T] L2).
(*
#T #L1 @(f2_ind … rfw … L1 T) -L1 -T
#n #IH #L1 * *
[ #k #Hn #L2 elim (eq_nat_dec (|L1|) (|L2|)) /3 width=1 by or_introl, lleq_sort/
| #i #H1 #L2 elim (eq_nat_dec (|L1|) (|L2|))
  [ #HL12 #d elim (lt_or_ge i d) /3 width=1 by lleq_skip, or_introl/
    #Hdi elim (lt_or_ge i (|L1|))
    #HiL1 elim (lt_or_ge i (|L2|)) /3 width=1 by or_introl, lleq_free/
    #HiL2 elim (ldrop_O1_lt … HiL2)
    #I2 #K2 #V2 #HLK2 elim (ldrop_O1_lt … HiL1)
    #I1 #K1 #V1 #HLK1 elim (eq_bind2_dec I2 I1)
    [ #H2 elim (eq_term_dec V2 V1)
      [ #H3 elim (IH K1 V1 … K2 0) destruct
        /3 width=7 by lleq_lref, ldrop_fwd_rfw, or_introl/
      ]
    ]
    -IH #H3 @or_intror
    #H elim (lleq_inv_lref … H) -H [1,3,4,6,7,9: * ]
    [1,3,5,7,8,9: /3 width=4 by lt_to_le_to_lt, lt_refl_false/ ]
    #I0 #X1 #X2 #V0 #HLX1 #HLX2 #HX12
    lapply (ldrop_mono … HLX1 … HLK1) -HLX1 -HLK1
    lapply (ldrop_mono … HLX2 … HLK2) -HLX2 -HLK2
    #H #H0 destruct /2 width=1 by/
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
*)
(* Main properties **********************************************************)

axiom- lleq_trans: ∀d,T. Transitive … (lleq d T).
(*
#d #T #L1 #L #H elim H -d -T -L1 -L
/4 width=5 by lleq_fwd_length, lleq_gref, lleq_sort, trans_eq/
[ #L1 #L #d #i #Hid #HL1 #L2 #H lapply (lleq_fwd_length … H)
  #HL2 elim (lleq_inv_lref … H) -H /2 width=1 by lleq_skip/
| #I #L1 #L #K1 #K #V #d #i #Hdi #HLK1 #HLK #_ #IHK1 #L2 #H elim (lleq_inv_lref … H) -H
  [ -HLK1 -IHK1 * #HLi #_ elim (lt_refl_false i)
    /3 width=5 by ldrop_fwd_length_lt2, lt_to_le_to_lt/ (**) (* slow *)
  | -K1 -K #Hid elim (lt_refl_false i) /2 width=3 by lt_to_le_to_lt/
  | * #I0 #K0 #K2 #V0 #HLK0 #HLK2 #HK12 lapply (ldrop_mono … HLK0 … HLK) -L
    #H destruct /3 width=7 by lleq_lref/
  ]
| #L1 #L #d #i #HL1i #HLi #HL #L2 #H lapply (lleq_fwd_length … H)
  #HL2 elim (lleq_inv_lref … H) -H /2 width=1 by lleq_free/
| #a #I #L1 #L #V #T #d #_ #_ #IHV #IHT #L2 #H elim (lleq_inv_bind … H) -H
  /3 width=1 by lleq_bind/
| #I #L1 #L #V #T #d #_ #_ #IHV #IHT #L2 #H elim (lleq_inv_flat … H) -H
  /3 width=1 by lleq_flat/
]
qed-.
*)
theorem lleq_canc_sn: ∀L,L1,L2,T,d. L ⋕[d, T] L1→ L ⋕[d, T] L2 → L1 ⋕[d, T] L2.
/3 width=3 by lleq_trans, lleq_sym/ qed-.

theorem lleq_canc_dx: ∀L1,L2,L,T,d. L1 ⋕[d, T] L → L2 ⋕[d, T] L → L1 ⋕[d, T] L2.
/3 width=3 by lleq_trans, lleq_sym/ qed-.
