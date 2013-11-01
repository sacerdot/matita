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

lemma lleq_inv_lref_dx: ∀L1,L2,i. L1 ⋕[#i] L2 →
                        ∀I,K2,V. ⇩[0, i] L2 ≡ K2.ⓑ{I}V →
                        ∃∃K1. ⇩[0, i] L1 ≡ K1.ⓑ{I}V & K1 ⋕[V] K2.
#L1 #L2 #i #H #I #K2 #V #HLK2 elim (lleq_inv_lref … H) -H *
[ #_ #H elim (lt_refl_false i)
  /3 width=5 by ldrop_fwd_length_lt2, lt_to_le_to_lt/
| #I0 #K1 #K0 #V0 #HLK1 #HLK0 #HK10 lapply (ldrop_mono … HLK0 … HLK2) -L2
  #H destruct /2 width=3 by ex2_intro/
]
qed-.

lemma lleq_inv_lift: ∀L1,L2,U. L1 ⋕[U] L2 →
                     ∀K1,K2,d,e. ⇩[d, e] L1 ≡ K1 → ⇩[d, e] L2 ≡ K2 →
                     ∀T. ⇧[d, e] T ≡ U → K1 ⋕[T] K2.
#L1 #L2 #U #H elim H -L1 -L2 -U
[ #L1 #L2 #k #HL12 #K1 #K2 #d #e #HLK1 #HLK2 #X #H >(lift_inv_sort2 … H) -X
  lapply (ldrop_fwd_length_eq … HLK1 HLK2 HL12) -L1 -L2 -d -e
  /2 width=1 by lleq_sort/ (**) (* full auto fails *)
| #I #L1 #L2 #K #K0 #W #i #HLK #HLK0 #HK0 #IHK0 #K1 #K2 #d #e #HLK1 #HLK2 #X #H elim (lift_inv_lref2 … H) -H
  * #Hdei #H destruct [ -HK0 | -IHK0 ]
  [ elim (ldrop_conf_lt … HLK1 … HLK) // -L1 #L1 #V #HKL1 #KL1 #HV0
    elim (ldrop_conf_lt … HLK2 … HLK0) // -Hdei -L2 #L2 #V2 #HKL2 #K0L2 #HV02
    lapply (lift_inj … HV02 … HV0) -HV02 #H destruct /3 width=11 by lleq_lref/
  | lapply (ldrop_conf_ge … HLK1 … HLK ?) // -L1
    lapply (ldrop_conf_ge … HLK2 … HLK0 ?) // -Hdei -L2
    /2 width=7 by lleq_lref/
  ]
| #L1 #L2 #i #HL1 #HL2 #HL12 #K1 #K2 #d #e #HLK1 #HLK2 #X #H elim (lift_inv_lref2 … H) -H
  * #_ #H destruct
  lapply (ldrop_fwd_length_eq … HLK1 HLK2 HL12)
  [ /4 width=3 by lleq_free, ldrop_fwd_length_le4, transitive_le/
  | lapply (ldrop_fwd_length … HLK1) -HLK1 #H >H in HL1; -H
    lapply (ldrop_fwd_length … HLK2) -HLK2 #H >H in HL2; -H
    /3 width=1 by lleq_free, le_plus_to_minus_r/
  ]
| #L1 #L2 #p #HL12 #K1 #K2 #d #e #HLK1 #HLK2 #X #H >(lift_inv_gref2 … H) -X
  lapply (ldrop_fwd_length_eq … HLK1 HLK2 HL12) -L1 -L2 -d -e
  /2 width=1 by lleq_gref/ (**) (* full auto fails *)
| #a #I #L1 #L2 #W #U #_ #_ #IHW #IHU #K1 #K2 #d #e #HLK1 #HLK2 #X #H elim (lift_inv_bind2 … H) -H
  #V #T #HVW #HTU #H destruct /4 width=5 by lleq_bind, ldrop_skip/
| #I #L1 #L2 #W #U #_ #_ #IHW #IHU #K1 #K2 #d #e #HLK1 #HLK2 #X #H elim (lift_inv_flat2 … H) -H
  #V #T #HVW #HTU #H destruct /3 width=5 by lleq_flat/
]
qed-.

(* Advanced properties ******************************************************)

lemma lleq_dec: ∀T,L1,L2. Decidable (L1 ⋕[T] L2).
#T #L1 @(f2_ind … rfw … L1 T) -L1 -T
#n #IH #L1 * *
[ #k #Hn #L2 elim (eq_nat_dec (|L1|) (|L2|)) /3 width=1 by or_introl, lleq_sort/
| #i #H1 #L2 elim (eq_nat_dec (|L1|) (|L2|))
  [ #HL12 elim (lt_or_ge i (|L1|))
    #HiL1 elim (lt_or_ge i (|L2|)) /3 width=1 by or_introl, lleq_free/
    #HiL2 elim (ldrop_O1_lt … HiL2)
    #I2 #K2 #V2 #HLK2 elim (ldrop_O1_lt … HiL1)
    #I1 #K1 #V1 #HLK1 elim (eq_bind2_dec I2 I1)
    [ #H2 elim (eq_term_dec V2 V1)
      [ #H3 elim (IH K1 V1 … K2) destruct
        /3 width=7 by lleq_lref, ldrop_fwd_rfw, or_introl/
      ]
    ]
    -IH #H3 @or_intror
    #H elim (lleq_inv_lref … H) -H *
    [1,3,5: /3 width=4 by lt_to_le_to_lt, lt_refl_false/ ]
    #I0 #X1 #X2 #V0 #HLX1 #HLX2 #HX12
    lapply (ldrop_mono … HLX1 … HLK1) -HLX1 -HLK1
    lapply (ldrop_mono … HLX2 … HLK2) -HLX2 -HLK2
    #H #H0 destruct /2 width=1 by/
  ]
| #p #Hn #L2 elim (eq_nat_dec (|L1|) (|L2|)) /3 width=1 by or_introl, lleq_gref/
| #a #I #V #T #Hn #L2 destruct
  elim (IH L1 V … L2) /2 width=1 by/
  elim (IH (L1.ⓑ{I}V) T … (L2.ⓑ{I}V)) -IH /3 width=1 by or_introl, lleq_bind/
  #H1 #H2 @or_intror
  #H elim (lleq_inv_bind … H) -H /2 width=1 by/
| #I #V #T #Hn #L2 destruct
  elim (IH L1 V … L2) /2 width=1 by/
  elim (IH L1 T … L2) -IH /3 width=1 by or_introl, lleq_flat/
  #H1 #H2 @or_intror
  #H elim (lleq_inv_flat … H) -H /2 width=1 by/
]
-n /4 width=2 by lleq_fwd_length, or_intror/
qed-.

(* Main properties **********************************************************)

theorem lleq_trans: ∀T. Transitive … (lleq T).
#T #L1 #L #H elim H -T -L1 -L
/4 width=4 by lleq_fwd_length, lleq_gref, lleq_sort, trans_eq/
[ #I #L1 #L #K1 #K #V #i #HLK1 #HLK #_ #IHK1 #L2 #H elim (lleq_inv_lref … H) -H *
  [ -HLK1 -IHK1 #HLi #_ elim (lt_refl_false i)
    /3 width=5 by ldrop_fwd_length_lt2, lt_to_le_to_lt/
  | #I0 #K0 #K2 #V0 #HLK0 #HLK2 #HK12 lapply (ldrop_mono … HLK0 … HLK) -L
    #H destruct /3 width=7 by lleq_lref/
  ]
| #L1 #L #i #HL1i #HLi #HL #L2 #H lapply (lleq_fwd_length … H)
  #HL2 elim (lleq_inv_lref … H) -H * /2 width=1 by lleq_free/
| #a #I #L1 #L #V #T #_ #_ #IHV #IHT #L2 #H elim (lleq_inv_bind … H) -H
  /3 width=1 by lleq_bind/
| #I #L1 #L #V #T #_ #_ #IHV #IHT #L2 #H elim (lleq_inv_flat … H) -H
  /3 width=1 by lleq_flat/
]
qed-.

theorem lleq_canc_sn: ∀L,L1,L2,T. L ⋕[T] L1→ L ⋕[T] L2 → L1 ⋕[T] L2.
/3 width=3 by lleq_trans, lleq_sym/ qed-.

theorem lleq_canc_dx: ∀L1,L2,L,T. L1 ⋕[T] L → L2 ⋕[T] L → L1 ⋕[T] L2.
/3 width=3 by lleq_trans, lleq_sym/ qed-.
