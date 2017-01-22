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

include "basic_2/unfold/tpss_tpss.ma".
include "basic_2/unfold/ltpss_dx_tpss.ma".
include "basic_2/static/ssta_lift.ma".

(* STRATIFIED STATIC TYPE ASSIGNMENT ON TERMS *******************************)

(* Properties about dx parallel unfold **************************************)

(* Note: apparently this was missing in basic_1 *)
lemma ssta_ltpss_dx_tpss_conf: ∀h,g,L1,T1,U1,l. ⦃h, L1⦄ ⊢ T1 •[g] ⦃l, U1⦄ →
                               ∀L2,d,e. L1 ▶* [d, e] L2 →
                               ∀T2. L2 ⊢ T1 ▶* [d, e] T2 →
                               ∃∃U2. ⦃h, L2⦄ ⊢ T2 •[g] ⦃l, U2⦄ &
                                     L2 ⊢ U1 ▶* [d, e] U2.
#h #g #L1 #T1 #U #l #H elim H -L1 -T1 -U -l
[ #L1 #k1 #l1 #Hkl1 #L2 #d #e #_ #T2 #H
  >(tpss_inv_sort1 … H) -H /3 width=3/
| #L1 #K1 #V1 #W1 #U1 #i #l #HLK1 #HVW1 #HWU1 #IHVW1 #L2 #d #e #HL12 #T2 #H
  elim (tpss_inv_lref1 … H) -H [ | -HVW1 ]
  [ #H destruct
    elim (lt_or_ge i d) #Hdi [ -HVW1 | ]
    [ elim (ltpss_dx_ldrop_conf_le … HL12 … HLK1 ?) -L1 /2 width=2/ #X #H #HLK2
      elim (ltpss_dx_inv_tpss11 … H ?) -H /2 width=1/ #K2 #V2 #HK12 #HV12 #H destruct
      elim (IHVW1 … HK12 … HV12) -IHVW1 -HK12 -HV12 #W2 #HVW2 #HW12
      lapply (ldrop_fwd_ldrop2 … HLK2) #H
      elim (lift_total W2 0 (i+1)) #U2 #HWU2
      lapply (tpss_lift_ge … HW12 … H … HWU1 … HWU2) // -HW12 -H -HWU1
      >minus_plus <plus_minus_m_m // -Hdi /3 width=6/
    | elim (lt_or_ge i (d + e)) #Hide [ -HVW1 | -Hdi -IHVW1 ]
      [ elim (ltpss_dx_ldrop_conf_be … HL12 … HLK1 ? ?) -L1 // /2 width=2/ #X #H #HLK2
        elim (ltpss_dx_inv_tpss21 … H ?) -H /2 width=1/ #K2 #V2 #HK12 #HV12 #H destruct
        elim (IHVW1 … HK12 … HV12) -IHVW1 -HK12 -HV12 #W2 #HVW2 #HW12
        lapply (ldrop_fwd_ldrop2 … HLK2) #H
        elim (lift_total W2 0 (i+1)) #U2 #HWU2
        lapply (tpss_lift_ge … HW12 … H … HWU1 … HWU2) // -HW12 -H -HWU1 >minus_plus #H
        lapply (tpss_weak … H d e ? ?) [1,2: normalize [ >commutative_plus <plus_minus_m_m // | /2 width=1/ ]] -Hdi -Hide /3 width=6/
      | lapply (ltpss_dx_ldrop_conf_ge … HL12 … HLK1 ?) -L1 // -Hide /3 width=6/
      ]
    ]
  | * #K2 #V2 #W2 #Hdi #Hide #HLK2 #HVW2 #HWT2
    elim (ltpss_dx_ldrop_conf_be … HL12 … HLK1 ? ?) -L1 // /2 width=2/ #X #H #HL2K0
    elim (ltpss_dx_inv_tpss21 … H ?) -H /2 width=1/ #K0 #V0 #HK12 #HV12 #H destruct
    lapply (ldrop_mono … HL2K0 … HLK2) -HL2K0 #H destruct
    lapply (ldrop_fwd_ldrop2 … HLK2) -HLK2 #HLK2
    lapply (tpss_trans_eq … HV12 HVW2) -V2 #HV1W2
    elim (IHVW1 … HK12 … HV1W2) -IHVW1 -HK12 -HV1W2 #V2 #HWV2 #HW1V2
    elim (lift_total V2 0 (i+1)) #U2 #HVU2
    lapply (ssta_lift … HWV2 … HLK2 … HWT2 … HVU2) -HWV2 -HWT2 #HTU2
    lapply (tpss_lift_ge … HW1V2 … HLK2 … HWU1 … HVU2) // -HW1V2 -HLK2 -HWU1 -HVU2 >minus_plus #H
    lapply (tpss_weak … H d e ? ?) [1,2: normalize [ >commutative_plus <plus_minus_m_m // | /2 width=1/ ]] -Hdi -Hide /2 width=3/
  ]
| #L1 #K1 #W1 #V1 #U1 #i #l #HLK1 #HWV1 #HWU1 #IHWV1 #L2 #d #e #HL12 #T2 #H
  elim (tpss_inv_lref1 … H) -H [ | -HWV1 -HWU1 -IHWV1 ]
  [ #H destruct
    elim (lt_or_ge i d) #Hdi [ -HWV1 ]
    [ elim (ltpss_dx_ldrop_conf_le … HL12 … HLK1 ?) -L1 /2 width=2/ #X #H #HLK2
      elim (ltpss_dx_inv_tpss11 … H ?) -H /2 width=1/ #K2 #W2 #HK12 #HW12 #H destruct
      elim (IHWV1 … HK12 … HW12) -IHWV1 -HK12 #V2 #HWV2 #_
      lapply (ldrop_fwd_ldrop2 … HLK2) #HLK
      elim (lift_total W2 0 (i+1)) #U2 #HWU2
      lapply (tpss_lift_ge … HW12 … HLK … HWU1 … HWU2) // -HW12 -HLK -HWU1
      >minus_plus <plus_minus_m_m // -Hdi /3 width=6/
    | elim (lt_or_ge i (d + e)) #Hide [ -HWV1 | -IHWV1 -Hdi ]
      [ elim (ltpss_dx_ldrop_conf_be … HL12 … HLK1 ? ?) -L1 // /2 width=2/ #X #H #HLK2
        elim (ltpss_dx_inv_tpss21 … H ?) -H /2 width=1/ #K2 #W2 #HK12 #HW12 #H destruct
        elim (IHWV1 … HK12 … HW12) -IHWV1 -HK12 #V2 #HWV2 #_
        lapply (ldrop_fwd_ldrop2 … HLK2) #HLK
        elim (lift_total W2 0 (i+1)) #U2 #HWU2
        lapply (tpss_lift_ge … HW12 … HLK … HWU1 … HWU2) // -HW12 -HLK -HWU1 >minus_plus #H
        lapply (tpss_weak … H d e ? ?) [1,2: normalize [ >commutative_plus <plus_minus_m_m // | /2 width=1/ ]] -Hdi -Hide /3 width=6/
      | lapply (ltpss_dx_ldrop_conf_ge … HL12 … HLK1 ?) -L1 // -Hide /3 width=6/
      ]
    ]
  | * #K2 #V2 #W2 #Hdi #Hide #HLK2 #_ #_
    elim (ltpss_dx_ldrop_conf_be … HL12 … HLK1 ? ?) -L1 // /2 width=2/ #X #H #HL2K0
    elim (ltpss_dx_inv_tpss21 … H ?) -H /2 width=1/ -Hdi -Hide #K0 #V0 #_ #_ #H destruct
    lapply (ldrop_mono … HL2K0 … HLK2) -HL2K0 -HLK2 #H destruct
  ]
| #a #I #L1 #V1 #T1 #U1 #l #_ #IHTU1 #L2 #d #e #HL12 #X #H
  elim (tpss_inv_bind1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct
  elim (IHTU1 … HT12) -IHTU1 -HT12 /2 width=1/ -HL12 /3 width=5/
| #L1 #V1 #T1 #U1 #l #_ #IHTU1 #L2 #d #e #HL12 #X #H
  elim (tpss_inv_flat1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct
  elim (IHTU1 … HT12) -IHTU1 -HT12 // -HL12 /3 width=5/
| #L1 #W1 #T1 #U1 #l #_ #IHTU1 #L2 #d #e #HL12 #X #H
  elim (tpss_inv_flat1 … H) -H #W2 #T2 #HW12 #HT12 #H destruct
  elim (IHTU1 … HT12) -IHTU1 -HT12 // -HL12 /3 width=3/
]
qed.

lemma ssta_ltpss_dx_tps_conf: ∀h,g,L1,T1,U1,l. ⦃h, L1⦄ ⊢ T1 •[g] ⦃l, U1⦄ →
                              ∀L2,d,e. L1 ▶* [d, e] L2 →
                              ∀T2. L2 ⊢ T1 ▶ [d, e] T2 →
                              ∃∃U2. ⦃h, L2⦄ ⊢ T2 •[g] ⦃l, U2⦄ &
                                    L2 ⊢ U1 ▶* [d, e] U2.
/3 width=5/ qed.

lemma ssta_ltpss_dx_conf: ∀h,g,L1,T,U1,l. ⦃h, L1⦄ ⊢ T •[g] ⦃l, U1⦄ →
                          ∀L2,d,e. L1 ▶* [d, e] L2 →
                          ∃∃U2. ⦃h, L2⦄ ⊢ T •[g] ⦃l, U2⦄ & L2 ⊢ U1 ▶* [d, e] U2.
/2 width=5/ qed.

lemma ssta_tpss_conf: ∀h,g,L,T1,U1,l. ⦃h, L⦄ ⊢ T1 •[g] ⦃l, U1⦄ →
                      ∀T2,d,e. L ⊢ T1 ▶* [d, e] T2 →
                      ∃∃U2. ⦃h, L⦄ ⊢ T2 •[g] ⦃l, U2⦄ & L ⊢ U1 ▶* [d, e] U2.
/2 width=5/ qed.

lemma ssta_tps_conf: ∀h,g,L,T1,U1,l. ⦃h, L⦄ ⊢ T1 •[g] ⦃l, U1⦄ →
                     ∀T2,d,e. L ⊢ T1 ▶ [d, e] T2 →
                     ∃∃U2. ⦃h, L⦄ ⊢ T2 •[g] ⦃l, U2⦄ & L ⊢ U1 ▶* [d, e] U2.
/2 width=5/ qed.
