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

include "basic_2/substitution/ldrop_lbotr.ma".
include "basic_2/unfold/tpss_lift.ma".
include "basic_2/unfold/delift.ma".

(* INVERSE BASIC TERM RELOCATION  *******************************************)

(* Advanced properties ******************************************************)

lemma delift_lref_be: ∀L,K,V1,V2,U2,i,d,e. d ≤ i → i < d + e →
                      ⇩[0, i] L ≡ K. ⓓV1 → K ⊢ ▼*[0, d + e - i - 1] V1 ≡ V2 →
                      ⇧[0, d] V2 ≡ U2 → L ⊢ ▼*[d, e] #i ≡ U2.
#L #K #V1 #V2 #U2 #i #d #e #Hdi #Hide #HLK * #V #HV1 #HV2 #HVU2
elim (lift_total V 0 (i+1)) #U #HVU
lapply (lift_trans_be … HV2 … HVU ? ?) -HV2 // >minus_plus <plus_minus_m_m /2 width=1/ #HV2U
lapply (lift_conf_be … HVU2 … HV2U ?) //
>commutative_plus in ⊢ (??%??→?); <minus_plus_m_m /3 width=6/
qed.

lemma lbotr_delift: ∀L,T1,d,e. d + e ≤ |L| → ⊒[d, e] L →
                    ∃T2. L ⊢ ▼*[d, e] T1 ≡ T2.
#L #T1 @(f2_ind … fw … L T1) -L -T1
#n #IH #L * * /2 width=2/
[ #i #H #d #e #Hde #HL destruct
  elim (lt_or_ge i d) #Hdi [ /3 width=2/ ]
  elim (lt_or_ge i (d+e)) #Hide [2: /3 width=2/ ]
  lapply (lt_to_le_to_lt … Hide Hde) #Hi
  elim (ldrop_O1_lt … Hi) -Hi #I #K #V1 #HLK
  lapply (lbotr_inv_ldrop … HLK … HL ? ?) // #H destruct
  lapply (ldrop_pair2_fwd_fw … HLK (#i)) #HKL
  lapply (ldrop_fwd_ldrop2 … HLK) #HLK0
  lapply (ldrop_fwd_O1_length … HLK0) #H
  lapply (lbotr_ldrop_trans_be_up … HLK0 … HL ? ?) -HLK0 -HL
  [1,2: /2 width=1/ | <minus_n_O <minus_plus ] #HK
  elim (IH … HKL … HK) -IH -HKL -HK
  [2: >H -H /2 width=1/ ] -Hde -H #V2 #V12 (**) (* H erased two times *)
  elim (lift_total V2 0 d) /3 width=7/
| #a #I #V1 #T1 #H #d #e #Hde #HL destruct
  elim (IH … V1 … Hde HL) // #V2 #HV12
  elim (IH (L.ⓑ{I}V1) T1 … (d+1) e ??) -IH // [2,3: /2 width=1/ ] -Hde -HL #T2 #HT12
  lapply (delift_lsubr_trans … HT12 (L.ⓑ{I}V2) ?) -HT12 /2 width=1/ /3 width=4/
| #I #V1 #T1 #H #d #e #Hde #HL destruct
  elim (IH … V1 … Hde HL) // #V2 #HV12
  elim (IH … T1 … Hde HL) -IH -Hde -HL // /3 width=2/
]
qed-.

(* Advanced inversion lemmas ************************************************)

lemma delift_inv_lref1_lt: ∀L,U2,i,d,e. L ⊢ ▼*[d, e] #i ≡ U2 → i < d → U2 = #i.
#L #U2 #i #d #e * #U #HU #HU2 #Hid
elim (tpss_inv_lref1 … HU) -HU
[ #H destruct >(lift_inv_lref2_lt … HU2) //
| * #K #V1 #V2 #Hdi
  lapply (lt_to_le_to_lt … Hid Hdi) -Hid -Hdi #Hi
  elim (lt_refl_false … Hi)
]
qed-.

lemma delift_inv_lref1_be: ∀L,U2,d,e,i. L ⊢ ▼*[d, e] #i ≡ U2 →
                           d ≤ i → i < d + e →
                           ∃∃K,V1,V2. ⇩[0, i] L ≡ K. ⓓV1 &
                                      K ⊢ ▼*[0, d + e - i - 1] V1 ≡ V2 &
                                      ⇧[0, d] V2 ≡ U2.
#L #U2 #d #e #i * #U #HU #HU2 #Hdi #Hide
elim (tpss_inv_lref1 … HU) -HU
[ #H destruct elim (lift_inv_lref2_be … HU2 ? ?) //
| * #K #V1 #V #_ #_ #HLK #HV1 #HVU
  elim (lift_div_be … HVU … HU2 ? ?) -U // /2 width=1/ /3 width=6/
]
qed-.

lemma delift_inv_lref1_ge: ∀L,U2,i,d,e. L ⊢ ▼*[d, e] #i ≡ U2 →
                           d + e ≤ i → U2 = #(i - e).
#L #U2 #i #d #e * #U #HU #HU2 #Hdei
elim (tpss_inv_lref1 … HU) -HU
[ #H destruct >(lift_inv_lref2_ge … HU2) //
| * #K #V1 #V2 #_ #Hide
  lapply (lt_to_le_to_lt … Hide Hdei) -Hide -Hdei #Hi
  elim (lt_refl_false … Hi)
]
qed-.

lemma delift_inv_lref1: ∀L,U2,i,d,e. L ⊢ ▼*[d, e] #i ≡ U2 →
                        ∨∨ (i < d ∧ U2 = #i)
                        |  (∃∃K,V1,V2. d ≤ i & i < d + e &
                                       ⇩[0, i] L ≡ K. ⓓV1 &
                                       K ⊢ ▼*[0, d + e - i - 1] V1 ≡ V2 &
                                       ⇧[0, d] V2 ≡ U2
                           )
                        |  (d + e ≤ i ∧ U2 = #(i - e)).
#L #U2 #i #d #e #H
elim (lt_or_ge i d) #Hdi
[ elim (delift_inv_lref1_lt … H Hdi) -H /3 width=1/
| elim (lt_or_ge i (d+e)) #Hide
  [ elim (delift_inv_lref1_be … H Hdi Hide) -H /3 width=6/
  | elim (delift_inv_lref1_ge … H Hide) -H /3 width=1/
  ]
]
qed-.

(* Properties on basic term relocation **************************************)

lemma delift_lift_le: ∀K,T1,T2,dt,et. K ⊢ ▼*[dt, et] T1 ≡ T2 →
                      ∀L,U1,d,e. dt + et ≤ d → ⇩[d, e] L ≡ K →
                      ⇧[d, e] T1 ≡ U1 → ∀U2. ⇧[d - et, e] T2 ≡ U2 →
                      L ⊢ ▼*[dt, et] U1 ≡ U2.
#K #T1 #T2 #dt #et * #T #HT1 #HT2 #L #U1 #d #e #Hdetd #HLK #HTU1 #U2 #HTU2
elim (lift_total T d e) #U #HTU
lapply (tpss_lift_le … HT1 … HLK HTU1 … HTU) -T1 -HLK // #HU1
elim (lift_trans_ge … HT2 … HTU ?) -T // -Hdetd #T #HT2 #HTU
>(lift_mono … HTU2 … HT2) -T2 /2 width=3/
qed.

lemma delift_lift_be: ∀K,T1,T2,dt,et. K ⊢ ▼*[dt, et] T1 ≡ T2 →
                      ∀L,U1,d,e. dt ≤ d → d ≤ dt + et →
                      ⇩[d, e] L ≡ K → ⇧[d, e] T1 ≡ U1 →
                      L ⊢ ▼*[dt, et + e] U1 ≡ T2.
#K #T1 #T2 #dt #et * #T #HT1 #HT2 #L #U1 #d #e #Hdtd #Hddet #HLK #HTU1
elim (lift_total T d e) #U #HTU
lapply (tpss_lift_be … HT1 … HLK HTU1 … HTU) -T1 -HLK // #HU1
lapply (lift_trans_be … HT2 … HTU ? ?) -T // -Hdtd -Hddet /2 width=3/
qed.

lemma delift_lift_ge: ∀K,T1,T2,dt,et. K ⊢ ▼*[dt, et] T1 ≡ T2 →
                      ∀L,U1,d,e. d ≤ dt → ⇩[d, e] L ≡ K →
                      ⇧[d, e] T1 ≡ U1 → ∀U2. ⇧[d, e] T2 ≡ U2 →
                      L ⊢ ▼*[dt + e, et] U1 ≡ U2.
#K #T1 #T2 #dt #et * #T #HT1 #HT2 #L #U1 #d #e #Hddt #HLK #HTU1 #U2 #HTU2
elim (lift_total T d e) #U #HTU
lapply (tpss_lift_ge … HT1 … HLK HTU1 … HTU) -T1 -HLK // #HU1
elim (lift_trans_le … HT2 … HTU ?) -T // -Hddt #T #HT2 #HTU
>(lift_mono … HTU2 … HT2) -T2 /2 width=3/
qed.

lemma delift_inv_lift1_eq: ∀L,U1,T2,d,e. L ⊢ ▼*[d, e] U1 ≡ T2 →
                           ∀K. ⇩[d, e] L ≡ K → ∀T1. ⇧[d, e] T1 ≡ U1 → T1 = T2.
#L #U1 #T2 #d #e * #U2 #HU12 #HTU2 #K #HLK #T1 #HTU1
lapply (tpss_inv_lift1_eq … HU12 … HTU1) -L -K #H destruct
lapply (lift_inj … HTU1 … HTU2) -U2 //
qed-.

lemma delift_lift_div_be: ∀L,T1,T,d,e,i. L ⊢ ▼*[i, d + e - i] T1 ≡ T →
                          ∀T2. ⇧[d, i - d] T2 ≡ T → d ≤ i → i ≤ d + e →
                          L ⊢ ▼*[d, e] T1 ≡ T2.
#L #T1 #T #d #e #i * #T0 #HT10 #HT0 #T2 #HT2 #Hdi #Hide
lapply (tpss_weak … HT10 d e ? ?) -HT10 // [ >commutative_plus /2 width=1/ ] #HT10
lapply (lift_trans_be … HT2 … HT0 ? ?) -T //
>commutative_plus >commutative_plus in ⊢ (? ? (? % ?) ? ? → ?);
<minus_le_minus_minus_comm // <plus_minus_m_m [ /2 width=3/ | /2 width=1/ ]
qed.
