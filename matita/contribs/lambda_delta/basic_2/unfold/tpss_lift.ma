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

include "basic_2/substitution/tps_lift.ma".
include "basic_2/unfold/tpss.ma".

(* PARTIAL UNFOLD ON TERMS **************************************************)

(* Advanced properties ******************************************************)

lemma tpss_subst: ∀L,K,V,U1,i,d,e.
                  d ≤ i → i < d + e →
                  ⇩[0, i] L ≡ K. ⓓV → K ⊢ V ▶* [0, d + e - i - 1] U1 →
                  ∀U2. ⇧[0, i + 1] U1 ≡ U2 → L ⊢ #i ▶* [d, e] U2.
#L #K #V #U1 #i #d #e #Hdi #Hide #HLK #H @(tpss_ind … H) -U1
[ /3 width=4/
| #U #U1 #_ #HU1 #IHU #U2 #HU12
  elim (lift_total U 0 (i+1)) #U0 #HU0
  lapply (IHU … HU0) -IHU #H
  lapply (ldrop_fwd_ldrop2 … HLK) -HLK #HLK
  lapply (tps_lift_ge … HU1 … HLK HU0 HU12 ?) -HU1 -HLK -HU0 -HU12 // normalize #HU02
  lapply (tps_weak … HU02 d e ? ?) -HU02 [ >minus_plus >commutative_plus /2 width=1/ | /2 width=1/ | /2 width=3/ ]
]
qed.

(* Advanced inverion lemmas *************************************************)

lemma tpss_inv_atom1: ∀L,T2,I,d,e. L ⊢ ⓪{I} ▶* [d, e] T2 →
                      T2 = ⓪{I} ∨
                      ∃∃K,V1,V2,i. d ≤ i & i < d + e &
                                   ⇩[O, i] L ≡ K. ⓓV1 &
                                   K ⊢ V1 ▶* [0, d + e - i - 1] V2 &
                                   ⇧[O, i + 1] V2 ≡ T2 &
                                   I = LRef i.
#L #T2 #I #d #e #H @(tpss_ind … H) -T2
[ /2 width=1/
| #T #T2 #_ #HT2 *
  [ #H destruct
    elim (tps_inv_atom1 … HT2) -HT2 [ /2 width=1/ | * /3 width=10/ ]
  | * #K #V1 #V #i #Hdi #Hide #HLK #HV1 #HVT #HI
    lapply (ldrop_fwd_ldrop2 … HLK) #H
    elim (tps_inv_lift1_ge_up … HT2 … H … HVT ? ? ?) normalize -HT2 -H -HVT [2,3,4: /2 width=1/ ] #V2 <minus_plus #HV2 #HVT2
    @or_intror @(ex6_4_intro … Hdi Hide HLK … HVT2 HI) /2 width=3/ (**) (* /4 width=10/ is too slow *)
  ]
]
qed-.

lemma tpss_inv_lref1: ∀L,T2,i,d,e. L ⊢ #i ▶* [d, e] T2 →
                      T2 = #i ∨
                      ∃∃K,V1,V2. d ≤ i & i < d + e &
                                 ⇩[O, i] L ≡ K. ⓓV1 &
                                 K ⊢ V1 ▶* [0, d + e - i - 1] V2 &
                                 ⇧[O, i + 1] V2 ≡ T2.
#L #T2 #i #d #e #H
elim (tpss_inv_atom1 … H) -H /2 width=1/
* #K #V1 #V2 #j #Hdj #Hjde #HLK #HV12 #HVT2 #H destruct /3 width=6/
qed-.

lemma tpss_inv_S2: ∀L,T1,T2,d,e. L ⊢ T1 ▶* [d, e + 1] T2 →
                   ∀K,V. ⇩[0, d] L ≡ K. ⓛV → L ⊢ T1 ▶* [d + 1, e] T2.
#L #T1 #T2 #d #e #H #K #V #HLK @(tpss_ind … H) -T2 //
#T #T2 #_ #HT2 #IHT
lapply (tps_inv_S2 … HT2 … HLK) -HT2 -HLK /2 width=3/
qed-.

lemma tpss_inv_refl_SO2: ∀L,T1,T2,d. L ⊢ T1 ▶* [d, 1] T2 →
                         ∀K,V. ⇩[0, d] L ≡ K. ⓛV → T1 = T2.
#L #T1 #T2 #d #H #K #V #HLK @(tpss_ind … H) -T2 //
#T #T2 #_ #HT2 #IHT <(tps_inv_refl_SO2 … HT2 … HLK) //
qed-.

(* Relocation properties ****************************************************)

lemma tpss_lift_le: ∀K,T1,T2,dt,et. K ⊢ T1 ▶* [dt, et] T2 →
                    ∀L,U1,d,e. dt + et ≤ d → ⇩[d, e] L ≡ K →
                    ⇧[d, e] T1 ≡ U1 → ∀U2. ⇧[d, e] T2 ≡ U2 →
                    L ⊢ U1 ▶* [dt, et] U2.
#K #T1 #T2 #dt #et #H #L #U1 #d #e #Hdetd #HLK #HTU1 @(tpss_ind … H) -T2
[ #U2 #H >(lift_mono … HTU1 … H) -H //
| -HTU1 #T #T2 #_ #HT2 #IHT #U2 #HTU2
  elim (lift_total T d e) #U #HTU
  lapply (IHT … HTU) -IHT #HU1
  lapply (tps_lift_le … HT2 … HLK HTU HTU2 ?) -HT2 -HLK -HTU -HTU2 // /2 width=3/
]
qed.

lemma tpss_lift_be: ∀K,T1,T2,dt,et. K ⊢ T1 ▶* [dt, et] T2 →
                    ∀L,U1,d,e. dt ≤ d → d ≤ dt + et →
                    ⇩[d, e] L ≡ K → ⇧[d, e] T1 ≡ U1 →
                    ∀U2. ⇧[d, e] T2 ≡ U2 → L ⊢ U1 ▶* [dt, et + e] U2.
#K #T1 #T2 #dt #et #H #L #U1 #d #e #Hdtd #Hddet #HLK #HTU1 @(tpss_ind … H) -T2
[ #U2 #H >(lift_mono … HTU1 … H) -H //
| -HTU1 #T #T2 #_ #HT2 #IHT #U2 #HTU2
  elim (lift_total T d e) #U #HTU
  lapply (IHT … HTU) -IHT #HU1
  lapply (tps_lift_be … HT2 … HLK HTU HTU2 ? ?) -HT2 -HLK -HTU -HTU2 // /2 width=3/
]
qed.

lemma tpss_lift_ge: ∀K,T1,T2,dt,et. K ⊢ T1 ▶* [dt, et] T2 →
                    ∀L,U1,d,e. d ≤ dt → ⇩[d, e] L ≡ K →
                    ⇧[d, e] T1 ≡ U1 → ∀U2. ⇧[d, e] T2 ≡ U2 →
                    L ⊢ U1 ▶* [dt + e, et] U2.
#K #T1 #T2 #dt #et #H #L #U1 #d #e #Hddt #HLK #HTU1 @(tpss_ind … H) -T2
[ #U2 #H >(lift_mono … HTU1 … H) -H //
| -HTU1 #T #T2 #_ #HT2 #IHT #U2 #HTU2
  elim (lift_total T d e) #U #HTU
  lapply (IHT … HTU) -IHT #HU1
  lapply (tps_lift_ge … HT2 … HLK HTU HTU2 ?) -HT2 -HLK -HTU -HTU2 // /2 width=3/
]
qed.

lemma tpss_inv_lift1_le: ∀L,U1,U2,dt,et. L ⊢ U1 ▶* [dt, et] U2 →
                         ∀K,d,e. ⇩[d, e] L ≡ K → ∀T1. ⇧[d, e] T1 ≡ U1 →
                         dt + et ≤ d →
                         ∃∃T2. K ⊢ T1 ▶* [dt, et] T2 & ⇧[d, e] T2 ≡ U2.
#L #U1 #U2 #dt #et #H #K #d #e #HLK #T1 #HTU1 #Hdetd @(tpss_ind … H) -U2
[ /2 width=3/
| -HTU1 #U #U2 #_ #HU2 * #T #HT1 #HTU
  elim (tps_inv_lift1_le … HU2 … HLK … HTU ?) -HU2 -HLK -HTU // /3 width=3/
]
qed.

lemma tpss_inv_lift1_be: ∀L,U1,U2,dt,et. L ⊢ U1 ▶* [dt, et] U2 →
                         ∀K,d,e. ⇩[d, e] L ≡ K → ∀T1. ⇧[d, e] T1 ≡ U1 →
                         dt ≤ d → d + e ≤ dt + et →
                         ∃∃T2. K ⊢ T1 ▶* [dt, et - e] T2 & ⇧[d, e] T2 ≡ U2.
#L #U1 #U2 #dt #et #H #K #d #e #HLK #T1 #HTU1 #Hdtd #Hdedet @(tpss_ind … H) -U2
[ /2 width=3/
| -HTU1 #U #U2 #_ #HU2 * #T #HT1 #HTU
  elim (tps_inv_lift1_be … HU2 … HLK … HTU ? ?) -HU2 -HLK -HTU // /3 width=3/
]
qed.

lemma tpss_inv_lift1_ge: ∀L,U1,U2,dt,et. L ⊢ U1 ▶* [dt, et] U2 →
                         ∀K,d,e. ⇩[d, e] L ≡ K → ∀T1. ⇧[d, e] T1 ≡ U1 →
                         d + e ≤ dt →
                         ∃∃T2. K ⊢ T1 ▶* [dt - e, et] T2 & ⇧[d, e] T2 ≡ U2.
#L #U1 #U2 #dt #et #H #K #d #e #HLK #T1 #HTU1 #Hdedt @(tpss_ind … H) -U2
[ /2 width=3/
| -HTU1 #U #U2 #_ #HU2 * #T #HT1 #HTU
  elim (tps_inv_lift1_ge … HU2 … HLK … HTU ?) -HU2 -HLK -HTU // /3 width=3/
]
qed.

lemma tpss_inv_lift1_eq: ∀L,U1,U2,d,e.
                         L ⊢ U1 ▶* [d, e] U2 → ∀T1. ⇧[d, e] T1 ≡ U1 → U1 = U2.
#L #U1 #U2 #d #e #H #T1 #HTU1 @(tpss_ind … H) -U2 //
#U #U2 #_ #HU2 #IHU destruct
<(tps_inv_lift1_eq … HU2 … HTU1) -HU2 -HTU1 //
qed.

lemma tpss_inv_lift1_ge_up: ∀L,U1,U2,dt,et. L ⊢ U1 ▶* [dt, et] U2 →
                            ∀K,d,e. ⇩[d, e] L ≡ K → ∀T1. ⇧[d, e] T1 ≡ U1 →
                            d ≤ dt → dt ≤ d + e → d + e ≤ dt + et →
                            ∃∃T2. K ⊢ T1 ▶* [d, dt + et - (d + e)] T2 &
                                 ⇧[d, e] T2 ≡ U2.
#L #U1 #U2 #dt #et #H #K #d #e #HLK #T1 #HTU1 #Hddt #Hdtde #Hdedet @(tpss_ind … H) -U2
[ /2 width=3/
| -HTU1 #U #U2 #_ #HU2 * #T #HT1 #HTU
  elim (tps_inv_lift1_ge_up … HU2 … HLK … HTU ? ? ?) -HU2 -HLK -HTU // /3 width=3/
]
qed.

lemma tpss_inv_lift1_be_up: ∀L,U1,U2,dt,et. L ⊢ U1 ▶* [dt, et] U2 →
                            ∀K,d,e. ⇩[d, e] L ≡ K → ∀T1. ⇧[d, e] T1 ≡ U1 →
                            dt ≤ d → dt + et ≤ d + e →
                            ∃∃T2. K ⊢ T1 ▶* [dt, d - dt] T2 & ⇧[d, e] T2 ≡ U2.
#L #U1 #U2 #dt #et #H #K #d #e #HLK #T1 #HTU1 #Hdtd #Hdetde @(tpss_ind … H) -U2
[ /2 width=3/
| -HTU1 #U #U2 #_ #HU2 * #T #HT1 #HTU
  elim (tps_inv_lift1_be_up … HU2 … HLK … HTU ? ?) -HU2 -HLK -HTU // /3 width=3/
]
qed.

lemma tpss_inv_lift1_le_up: ∀L,U1,U2,dt,et. L ⊢ U1 ▶* [dt, et] U2 →
                            ∀K,d,e. ⇩[d, e] L ≡ K → ∀T1. ⇧[d, e] T1 ≡ U1 →
                            dt ≤ d → d ≤ dt + et → dt + et ≤ d + e →
                            ∃∃T2. K ⊢ T1 ▶* [dt, d - dt] T2 & ⇧[d, e] T2 ≡ U2.
#L #U1 #U2 #dt #et #H #K #d #e #HLK #T1 #HTU1 #Hdtd #Hddet #Hdetde @(tpss_ind … H) -U2
[ /2 width=3/
| -HTU1 #U #U2 #_ #HU2 * #T #HT1 #HTU
  elim (tps_inv_lift1_le_up … HU2 … HLK … HTU ? ? ?) -HU2 -HLK -HTU // /3 width=3/
]
qed.
