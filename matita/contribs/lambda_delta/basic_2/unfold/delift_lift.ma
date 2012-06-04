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

include "basic_2/unfold/tpss_lift.ma".
include "basic_2/unfold/delift.ma".

(* INVERSE BASIC TERM RELOCATION  *******************************************)

(* Advanced properties ******************************************************)

lemma delift_lref_be: ∀L,K,V1,V2,U2,i,d,e. d ≤ i → i < d + e →
                      ⇩[0, i] L ≡ K. ⓓV1 → K ⊢ V1 ▼*[0, d + e - i - 1] ≡ V2 →
                      ⇧[0, d] V2 ≡ U2 → L ⊢ #i ▼*[d, e] ≡ U2.
#L #K #V1 #V2 #U2 #i #d #e #Hdi #Hide #HLK * #V #HV1 #HV2 #HVU2
elim (lift_total V 0 (i+1)) #U #HVU
lapply (lift_trans_be … HV2 … HVU ? ?) -HV2 // >minus_plus <plus_minus_m_m /2 width=1/ #HV2U 
lapply (lift_conf_be … HVU2 … HV2U ?) //
>commutative_plus in ⊢ (??%??→?); <minus_plus_m_m /3 width=6/ 
qed.
 
(* Advanced inversion lemmas ************************************************)

lemma delift_inv_lref1_lt: ∀L,U2,i,d,e. L ⊢ #i ▼*[d, e] ≡ U2 → i < d → U2 = #i.
#L #U2 #i #d #e * #U #HU #HU2 #Hid
elim (tpss_inv_lref1 … HU) -HU
[ #H destruct >(lift_inv_lref2_lt … HU2) //
| * #K #V1 #V2 #Hdi
  lapply (lt_to_le_to_lt … Hid Hdi) -Hid -Hdi #Hi
  elim (lt_refl_false … Hi)
]
qed-.

lemma delift_inv_lref1_be: ∀L,U2,d,e,i. L ⊢ #i ▼*[d, e] ≡ U2 →
                           d ≤ i → i < d + e →
                           ∃∃K,V1,V2. ⇩[0, i] L ≡ K. ⓓV1 &
                                      K ⊢ V1 ▼*[0, d + e - i - 1] ≡ V2 &
                                      ⇧[0, d] V2 ≡ U2.
#L #U2 #d #e #i * #U #HU #HU2 #Hdi #Hide
elim (tpss_inv_lref1 … HU) -HU
[ #H destruct elim (lift_inv_lref2_be … HU2 ? ?) //
| * #K #V1 #V #_ #_ #HLK #HV1 #HVU
  elim (lift_div_be … HVU … HU2 ? ?) -U // /2 width=1/ /3 width=6/
]
qed-.

lemma delift_inv_lref1_ge: ∀L,U2,i,d,e. L ⊢ #i ▼*[d, e] ≡ U2 →
                           d + e ≤ i → U2 = #(i - e).
#L #U2 #i #d #e * #U #HU #HU2 #Hdei
elim (tpss_inv_lref1 … HU) -HU
[ #H destruct >(lift_inv_lref2_ge … HU2) //
| * #K #V1 #V2 #_ #Hide
  lapply (lt_to_le_to_lt … Hide Hdei) -Hide -Hdei #Hi
  elim (lt_refl_false … Hi)
]
qed-.

lemma delift_inv_lref1: ∀L,U2,i,d,e. L ⊢ #i ▼*[d, e] ≡ U2 →
                        ∨∨ (i < d ∧ U2 = #i) 
                        |  (∃∃K,V1,V2. d ≤ i & i < d + e &
                                       ⇩[0, i] L ≡ K. ⓓV1 &
                                       K ⊢ V1 ▼*[0, d + e - i - 1] ≡ V2 &
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

lemma delift_lift_le: ∀K,T1,T2,dt,et. K ⊢ T1 ▼*[dt, et] ≡ T2 →
                      ∀L,U1,d,e. dt + et ≤ d → ⇩[d, e] L ≡ K →
                      ⇧[d, e] T1 ≡ U1 → ∀U2. ⇧[d - et, e] T2 ≡ U2 →
                      L ⊢ U1 ▼*[dt, et] ≡ U2.
#K #T1 #T2 #dt #et * #T #HT1 #HT2 #L #U1 #d #e #Hdetd #HLK #HTU1 #U2 #HTU2
elim (lift_total T d e) #U #HTU
lapply (tpss_lift_le … HT1 … HLK HTU1 … HTU) -T1 -HLK // #HU1
elim (lift_trans_ge … HT2 … HTU ?) -T // -Hdetd #T #HT2 #HTU
>(lift_mono … HTU2 … HT2) -T2 /2 width=3/
qed.

lemma delift_lift_be: ∀K,T1,T2,dt,et. K ⊢ T1 ▼*[dt, et] ≡ T2 →
                      ∀L,U1,d,e. dt ≤ d → d ≤ dt + et →
                      ⇩[d, e] L ≡ K → ⇧[d, e] T1 ≡ U1 →
                      L ⊢ U1 ▼*[dt, et + e] ≡ T2.
#K #T1 #T2 #dt #et * #T #HT1 #HT2 #L #U1 #d #e #Hdtd #Hddet #HLK #HTU1
elim (lift_total T d e) #U #HTU
lapply (tpss_lift_be … HT1 … HLK HTU1 … HTU) -T1 -HLK // #HU1
lapply (lift_trans_be … HT2 … HTU ? ?) -T // -Hdtd -Hddet /2 width=3/
qed.

lemma delift_lift_ge: ∀K,T1,T2,dt,et. K ⊢ T1 ▼*[dt, et] ≡ T2 →
                      ∀L,U1,d,e. d ≤ dt → ⇩[d, e] L ≡ K →
                      ⇧[d, e] T1 ≡ U1 → ∀U2. ⇧[d, e] T2 ≡ U2 →
                      L ⊢ U1 ▼*[dt + e, et] ≡ U2.
#K #T1 #T2 #dt #et * #T #HT1 #HT2 #L #U1 #d #e #Hddt #HLK #HTU1 #U2 #HTU2
elim (lift_total T d e) #U #HTU
lapply (tpss_lift_ge … HT1 … HLK HTU1 … HTU) -T1 -HLK // #HU1
elim (lift_trans_le … HT2 … HTU ?) -T // -Hddt #T #HT2 #HTU
>(lift_mono … HTU2 … HT2) -T2 /2 width=3/
qed.

lemma delift_inv_lift1_eq: ∀L,U1,T2,d,e. L ⊢ U1 ▼*[d, e] ≡ T2 →
                           ∀K. ⇩[d, e] L ≡ K → ∀T1. ⇧[d, e] T1 ≡ U1 → T1 = T2.
#L #U1 #T2 #d #e * #U2 #HU12 #HTU2 #K #HLK #T1 #HTU1
lapply (tpss_inv_lift1_eq … HU12 … HTU1) -L -K #H destruct
lapply (lift_inj … HTU1 … HTU2) -U2 //
qed-.

lemma delift_lift_div_be: ∀L,T1,T,d,e,i. L ⊢ T1 ▼*[i, d + e - i] ≡ T →
                          ∀T2. ⇧[d, i - d] T2 ≡ T → d ≤ i → i ≤ d + e →
                          L ⊢ T1 ▼*[d, e] ≡ T2.
#L #T1 #T #d #e #i * #T0 #HT10 #HT0 #T2 #HT2 #Hdi #Hide
lapply (tpss_weak … HT10 d e ? ?) -HT10 // [ >commutative_plus /2 width=1/ ] #HT10
lapply (lift_trans_be … HT2 … HT0 ? ?) -T //
>commutative_plus >commutative_plus in ⊢ (? ? (? % ?) ? ? → ?);
<minus_le_minus_minus_comm // <plus_minus_m_m [ /2 width=3/ | /2 width=1/ ]
qed.
