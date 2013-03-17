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

include "basic_2/equivalence/lsubss_ssta.ma".
include "basic_2/dynamic/snv_cpcs.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

(* Properties on context-free parallel reduction for local environments *****)

fact ssta_ltpr_tpr_aux: ∀h,g,L0,T0.
                        (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_snv_ssta h g L1 T1) →
                        (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_snv_ltpr_tpr h g L1 T1) →
                        (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_ssta_ltpr_tpr h g L1 T1) →
                        ∀L1,T1. L0 = L1 → T0 = T1 → IH_ssta_ltpr_tpr h g L1 T1.
#h #g #L0 #T0 #IH3 #IH2 #IH1 #L1 * * [|||| *]
[ #k #_ #_ #_ #X2 #l #H2 #L2 #HL12 #X3 #H3 -IH3 -IH2 -IH1
  elim (ssta_inv_sort1 … H2) -H2 #Hkl #H destruct
  >(tpr_inv_atom1 … H3) -X3 /4 width=6/
| #i #HL0 #HT0 #H1 #X2 #l #H2 #L2 #HL12 #X3 #H3 destruct -IH3 -IH2
  elim (snv_inv_lref … H1) -H1 #I0 #K0 #V0 #H #HV1
  elim (ssta_inv_lref1 … H2) -H2 * #K1
  >(tpr_inv_atom1 … H3) -X3
  [ #V1 #W1 #HLK1 #HVW1 #HWU1
    lapply (ldrop_mono … H … HLK1) -H #H destruct
    lapply (ldrop_pair2_fwd_fw … HLK1 (#i)) #HKV1
    elim (ltpr_ldrop_conf … HLK1 … HL12) -HLK1 -HL12 #X #H #HLK2
    elim (ltpr_inv_pair1 … H) -H #K2 #V2 #HK12 #HV12 #H destruct
    elim (IH1 … HVW1 … HK12 … HV12) -IH1 -HVW1 -HV12 // [2: /2 width=1/ ] -V1 #W2 #HVW2 #HW12
    lapply (ldrop_fwd_ldrop2 … HLK2) #H2
    elim (lift_total W2 0 (i+1)) #U2 #HWU2
    lapply (cpcs_lift … H2 … HWU1 … HWU2 HW12) -H2 -W1 /3 width=6/
  | #V1 #W1 #l0 #HLK1 #HVW1 #HVU1 #H destruct
    lapply (ldrop_mono … H … HLK1) -H #H destruct
    lapply (ldrop_pair2_fwd_fw … HLK1 (#i)) #HKV1
    elim (ltpr_ldrop_conf … HLK1 … HL12) -HLK1 #X #H #HLK2
    elim (ltpr_inv_pair1 … H) -H #K2 #V2 #HK12 #HV12 #H destruct
    elim (IH1 … HVW1 … HK12 … HV12) -IH1 -HVW1 -HK12 // [2: /2 width=1/ ] -HV1 -HKV1 #W2 #HVW2 #_ -W1
    elim (lift_total V2 0 (i+1)) #U2 #HVU2
    lapply (tpr_lift … HV12 … HVU1 … HVU2) -V1 /4 width=6/
  ]
| #p #_ #HT0 #H1 destruct -IH3 -IH2 -IH1
  elim (snv_inv_gref … H1)
| #a #I #V1 #T1 #HL0 #HT0 #H1 #X2 #l #H2 #L2 #HL12 #X3 #H3 destruct -IH3 -IH2
  elim (snv_inv_bind … H1) -H1 #_ #HT1
  elim (ssta_inv_bind1 … H2) -H2 #U1 #HTU1 #H destruct
  elim (tpr_inv_bind1 … H3) -H3 *
  [ #V2 #T0 #T2 #HV12 #HT10 #HT02 #H destruct
    lapply (tps_lsubr_trans … HT02 (L2.ⓑ{I}V2) ?) -HT02 [ /2 width=1/ ] #HT02
    elim (ssta_ltpr_cpr_aux … HT1 … HTU1 (L2.ⓑ{I}V2) … T2) -HT1 -HTU1
    [2: /3 width=5 by cpr_intro, tps_tpss/ |3: /2 width=1/ |4: /3 width=1/ ] -IH1 -T0 -HL12 #U2 #HTU2 #HU12
    lapply (cpcs_bind2 … V1 … HU12 … a) -HU12 [ /2 width=1/ ] -HV12 /3 width=3/
  | #T2 #HT12 #HT2 #H1 #H2 destruct
    elim (IH1 … HTU1 (L2.ⓓV1) … T2) -IH1 -HTU1 // [2,3: /2 width=1/ ] -T1 -HL12 #U2 #HTU2 #HU12
    lapply (cpcs_bind1 … HU12 … V1 … true) // -HU12 #HU12
    elim (ssta_inv_lift1 … HTU2 … HT2) -T2 [3: /2 width=1/ |2: skip ] #U #HXU #HU2
    lapply (cpcs_cpr_strap1 … HU12 U ?) -HU12 [ /3 width=3/ ] -U2 /2 width=3/
  ]
| #V1 #T1 #HL0 #HT0 #H1 #X2 #l #H2 #L2 #HL12 #X3 #H3 destruct
  elim (snv_inv_appl … H1) -H1 #a #W1 #W10 #U10 #l0 #HV1 #HT1 #HVW1 #HW10 #HTU10
  elim (ssta_inv_appl1 … H2) -H2 #U1 #HTU1 #H destruct
  elim (tpr_inv_appl1 … H3) -H3 *
  [ #V2 #T2 #HV12 #HT12 #H destruct -a -l0 -W1 -W10 -U10 -HV1 -IH3 -IH2
    elim (IH1 … HTU1 … HL12 … HT12) -IH1 -HTU1 -HL12 // [2: /2 width=1/ ] -T1 #U2 #HTU2 #HU12
    lapply (cpcs_flat … V1 V2 … HU12) -HU12 [ /2 width=1/ ] -HV12 /3 width=3/
  | #b #V2 #W #T2 #T20 #HV12 #HT20 #H1 #H2 destruct
    elim (snv_inv_bind … HT1) -HT1 #HW #HT2
    elim (ssta_inv_bind1 … HTU1) -HTU1 #U2 #HTU2 #H destruct
    elim (dxprs_inv_abst1 … HTU10) -HTU10 #W0 #U0 #HW0 #_ #H destruct
    lapply (cprs_div … HW10 … HW0) -W0 #HW1W
    elim (ssta_fwd_correct … HVW1) <minus_plus_m_m #X1 #HWX1
    elim (snv_fwd_ssta … HW) #l1 #V #HWV
    lapply (IH3 … HVW1) -IH3 // [ /2 width=1/ ] #HW1
    elim (ssta_ltpr_cpcs_aux … IH2 IH1 … HWX1 … HWV …) -IH2 -HWX1 //
    [2: /2 width=1/ |3: /3 width=4 by ygt_strap1, fw_ygt, ypr_ssta/ ] #H #_ destruct -X1
    elim (IH1 … HVW1 … HL12 … HV12) -HVW1 // -HV1 [2: /2 width=1/ ] #W2 #HVW2 #HW12
    elim (IH1 … HWV … HL12 W) -HWV // -HW [2: /2 width=1/ ] #V0 #HWV0 #_
    elim (IH1 … HTU2 (L2.ⓛW) … HT20) -IH1 -HTU2 -HT20 // [2,3: /2 width=1/ ] -HT2 #U20 #HTU20 #HU20
    lapply (ltpr_cpcs_conf … HL12 … HW1W) -L1 #HW1W
    lapply (cpcs_canc_sn … HW12 HW1W) -W1 #HW2
    elim (lsubss_ssta_trans … HTU20 (L2.ⓓV2) ?) -HTU20
    [ #U #HTU20 #HUU20 -HWV0 -W2
      @(ex2_intro … (ⓓ{b}V2.U)) [ /2 width=1/ ] -h -l -l1 -V -V0 -T2 -T20 -U0
      @(cpcs_cprs_strap2 … (ⓓ{b}V2.U2)) [ /3 width=1/ ] -V1
      @(cpcs_canc_dx … (ⓓ{b}V2.U20)) /2 width=2/
    | -b -l -V -V1 -T2 -T20 -U0 -U2 -U20 /2 width=6/
    ]
  | #b #V0 #V2 #W0 #W2 #T0 #T2 #HV10 #HW02 #HT02 #HV02 #H1 #H2 destruct -a -l0 -W1 -W10 -HV1 -IH3 -IH2
    elim (ssta_inv_bind1 … HTU1) -HTU1 #U0 #HTU0 #H destruct
    elim (snv_inv_bind … HT1) -HT1 #_ #HT0
    elim (IH1 … HTU0 (L2.ⓓW2) … HT02) -IH1 -HTU0 // [2,3: /2 width=1/ ] -T0 -HL12 #U2 #HTU2 #HU02
    lapply (cpcs_bind2 … W0 … HU02 b) -HU02 [ /2 width=1/ ] #HU02
    lapply (cpcs_flat … V1 V0 … HU02 Appl) [ /2 width=1/ ] -HV10 -HU02 #HU02
    lapply (cpcs_cpr_strap1 … HU02 (ⓓ{b}W2.ⓐV2.U2) ?) -HU02 [ /3 width=3/ ] -V0 -HW02 /4 width=3/
  ]
| #U0 #T1 #HL0 #HT0 #H1 #X2 #l #H2 #L2 #HL12 #X3 #H3 destruct -IH3 -IH2
  elim (snv_inv_cast … H1) -H1 #T0 #l0 #_ #HT1 #HT10 #_
  lapply (ssta_inv_cast1 … H2) -H2 #HTU1
  elim (ssta_mono … HT10 … HTU1) -HT10 #H1 #H2 destruct
  elim (tpr_inv_cast1 … H3) -H3
  [ * #U2 #T2 #_ #HT12 #H destruct
    elim (IH1 … HTU1 … HL12 … HT12) -IH1 -HTU1 -HL12 // [2: /2 width=1/ ] -T1 -U0 /3 width=3/
  | #HT1X3
    elim (IH1 … HTU1 … HL12 … HT1X3) -IH1 -HTU1 -HL12 // [2: /2 width=1/ ] -U0 -T1 /2 width=3/
  ]
]
qed-.
