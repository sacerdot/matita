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

include "basic_2/computation/cpds_cpds.ma".
include "basic_2/dynamic/snv_cpcs.ma".
include "basic_2/dynamic/lsubsv_ssta.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

(* Properties on sn parallel reduction for local environments ***************)

fact ssta_cpr_lpr_aux: ∀h,g,L0,T0.
                       (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[h, g] ⦃L1, T1⦄ → IH_snv_ssta h g L1 T1) →
                       (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[h, g] ⦃L1, T1⦄ → IH_snv_cpr_lpr h g L1 T1) →
                       (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[h, g] ⦃L1, T1⦄ → IH_ssta_cpr_lpr h g L1 T1) →
                       ∀L1,T1. L0 = L1 → T0 = T1 → IH_ssta_cpr_lpr h g L1 T1.
#h #g #L0 #T0 #IH3 #IH2 #IH1 #L1 * * [|||| *]
[ #k #_ #_ #_ #X2 #l #H2 #X3 #H3 #L2 #HL12 -IH3 -IH2 -IH1
  elim (ssta_inv_sort1 … H2) -H2 #Hkl #H destruct
  >(cpr_inv_sort1 … H3) -X3 /4 width=6/
| #i #HL0 #HT0 #H1 #X2 #l #H2 #X3 #H3 #L2 #HL12 destruct -IH3 -IH2
  elim (snv_inv_lref … H1) -H1 #I0 #K0 #V0 #H #HV1
  elim (ssta_inv_lref1 … H2) -H2 * #K1
  #V1 #W1 [| #l0 ] #HLK1 #HVW1 #HWU1 [| #H destruct ]
  lapply (ldrop_mono … H … HLK1) -H #H destruct
  lapply (fsupp_lref … HLK1) #HKV1
  elim (lpr_ldrop_conf … HLK1 … HL12) -HL12 #X #H #HLK2
  elim (lpr_inv_pair1 … H) -H #K2 #V2 #HK12 #HV12 #H destruct
  lapply (ldrop_fwd_ldrop2 … HLK2) #H2
  elim (cpr_inv_lref1 … H3) -H3
  [1,3: #H destruct -HLK1
  |2,4: * #K0 #V0 #W0 #H #HVW0 #HW0
        lapply (ldrop_mono … H … HLK1) -H -HLK1 #H destruct
  ]
  [ elim (IH1 … HVW1 … HV12 … HK12) -IH1 -HVW1 // [2: /2 width=1/ ] -K1 -V1 #W2 #HVW2 #HW12
    elim (lift_total W2 0 (i+1)) #U2 #HWU2
    lapply (cpcs_lift … H2 … HWU1 … HWU2 HW12) -H2 -W1 /3 width=6/
  | elim (IH1 … HVW1 … HV12 … HK12) -IH1 -HVW1 // [2: /2 width=1/ ] #W2 #HVW2 #_
    elim (lift_total V2 0 (i+1)) #U2 #HVU2
    lapply (lpr_cpr_conf … HK12 … HV12) -HV12 #HV12
    lapply (cpcs_lift … H2 … HWU1 … HVU2 HV12) -H2 -V1 /3 width=6/
  | elim (IH1 … HVW1 … HVW0 … HK12) -IH1 -HVW1 // [2: /2 width=1/ ] -K1 -V1 #W2 #HVW2 #HW12
    elim (lift_total W2 0 (i+1)) #U2 #HWU2
    lapply (ssta_lift … HVW2 … H2 … HW0 … HWU2) -HVW2 -HW0
    lapply (cpcs_lift … H2 … HWU1 … HWU2 HW12) -H2 -W1 /3 width=6/
  ]
| #p #_ #HT0 #H1 destruct -IH3 -IH2 -IH1
  elim (snv_inv_gref … H1)
| #a #I #V1 #T1 #HL0 #HT0 #H1 #X2 #l #H2 #X3 #H3 #L2 #HL12 destruct -IH3 -IH2
  elim (snv_inv_bind … H1) -H1 #_ #HT1
  elim (ssta_inv_bind1 … H2) -H2 #U1 #HTU1 #H destruct
  elim (cpr_inv_bind1 … H3) -H3 *
  [ #V2 #T2 #HV12 #HT12 #H destruct
    elim (IH1 … HTU1 … HT12 (L2.ⓑ{I}V2)) // [2,3: /2 width=1/ ] -T1
    lapply (lpr_cpr_conf … HL12 … HV12) -L1 /3 width=5/
  | #T2 #HT12 #HT2 #H1 #H2 destruct
    elim (IH1 … HTU1 … HT12 (L2.ⓓV1)) -IH1 -HTU1 // [2,3: /2 width=1/ ] -T1 -HL12 #U2 #HTU2 #HU12
    elim (ssta_inv_lift1 … HTU2 … HT2) -T2 [3: /2 width=1/ |2: skip ] #U #HXU #HU2
    lapply (cpcs_bind1 true … V1 V1 … HU12) // -HU12 #HU12
    lapply (cpcs_cpr_strap1 … HU12 U ?) -HU12 /2 width=3/
  ]
| #V1 #T1 #HL0 #HT0 #H1 #X2 #l #H2 #X3 #H3 #L2 #HL12 destruct
  elim (snv_inv_appl … H1) -H1 #a #W1 #W10 #U10 #l0 #HV1 #HT1 #HVW1 #HW10 #HTU10
  elim (ssta_inv_appl1 … H2) -H2 #U1 #HTU1 #H destruct
  elim (cpr_inv_appl1 … H3) -H3 *
  [ #V2 #T2 #HV12 #HT12 #H destruct -a -l0 -W1 -W10 -U10 -HV1 -IH3 -IH2
    elim (IH1 … HTU1 … HT12 … HL12) -IH1 -HTU1 // [2: /2 width=1/ ] -T1 #U2 #HTU2 #HU12
    lapply (lpr_cpr_conf … HL12 … HV12) -L1 /3 width=5/
  | #b #V2 #W2 #W20 #T2 #T20 #HV12 #HW20 #HT20 #H1 #H2 destruct
    elim (snv_inv_bind … HT1) -HT1 #HW2 #HT2
    elim (ssta_inv_bind1 … HTU1) -HTU1 #U2 #HTU2 #H destruct
    elim (cpds_inv_abst1 … HTU10) -HTU10 #W0 #U0 #HW0 #_ #H destruct
    lapply (cprs_div … HW10 … HW0) -W0 #HW12
    elim (ssta_fwd_correct … HVW1) <minus_plus_m_m #X1 #HWX1
    elim (snv_fwd_ssta … HW2) #l1 #V22 #HWV22
    lapply (IH3 … HVW1) -IH3 // [ /2 width=1/ ] #HW1
    elim (ssta_cpcs_lpr_aux … IH2 IH1 … HWX1 … HWV22 … L1) -HWX1 //
    [2: /2 width=1/
    |3: /4 width=4 by ygt_yprs_trans, fsupp_ygt, sstas_yprs, ssta_sstas/
    ] #H #_ destruct -X1
    lapply (IH2 … HV1 … HV12 … HL12) [ /2 width=1/ ] #HV2    
    lapply (IH2 … HW2 … HW20 … HL12) [ /2 width=1/ ] -IH2 #H2W20
    elim (IH1 … HVW1 … HV12 … HL12) -HVW1 // -HV1 [2: /2 width=1/ ] #W12 #HVW12 #HW112
    elim (IH1 … HWV22 … HW20 … HL12) -HWV22 // -HW2 [2: /2 width=1/ ] #V20 #HWV20 #_
    elim (IH1 … HTU2 … HT20 (L2.ⓛW20)) -IH1 -HTU2 -HT20 // [2,3: /2 width=1/ ] -HT2 #U20 #HTU20 #HU20
    lapply (lpr_cpcs_conf … HL12 … HW12) -HW12 #HW12
    lapply (lpr_cpr_conf … HL12 … HW20) -HW20 #HW20
    lapply (lpr_cpr_conf … HL12 … HV12) -L1 #HV12
    lapply (cpcs_canc_sn … HW12 HW112) -W1 #HW12
    lapply (cpcs_canc_sn … HW12 HW20) -HW12 #HW12
    elim (lsubsv_ssta_trans … HTU20 (L2.ⓓⓝW20.V2)) -HTU20
    [ #U #HTU20 #HUU20 -HVW12 -HWV20 -HW12
      @(ex2_intro … (ⓓ{b}ⓝW20.V2.U)) [ /3 width=1/ ] -HTU20
      @(cpcs_canc_dx … (ⓓ{b}ⓝW20.V2.U20)) [2: /2 width=1/ ] -HUU20
      @(cpcs_cpr_strap1 … (ⓐV2.ⓛ{b}W20.U20)) [2: /2 width=1/ ]
      /3 by cpcs_bind2, cpcs_flat/
    | -HU20 -HW20 -HV12 /3 width=5 by lsubsv_abbr, snv_cast/ 
    ]
  | #b #V0 #V2 #W0 #W2 #T0 #T2 #HV10 #HV02 #HW02 #HT02 #H1 #H2 destruct -a -l0 -W1 -W10 -HV1 -IH3 -IH2
    elim (ssta_inv_bind1 … HTU1) -HTU1 #U0 #HTU0 #H destruct
    elim (snv_inv_bind … HT1) -HT1 #_ #HT0
    elim (IH1 … HTU0 … HT02 (L2.ⓓW2)) -IH1 -HTU0 // [2,3: /2 width=1/ ] -T0 #U2 #HTU2 #HU02
    lapply (lpr_cpr_conf … HL12 … HV10) -HV10 #HV10
    lapply (lpr_cpr_conf … HL12 … HW02) -L1 #HW02
    lapply (cpcs_bind2 b … HW02 … HU02) -HW02 -HU02 #HU02
    lapply (cpcs_flat … HV10 … HU02 Appl) -HV10 -HU02 #HU02
    lapply (cpcs_cpr_strap1 … HU02 (ⓓ{b}W2.ⓐV2.U2) ?) [ /2 width=3/ ] -V0 /4 width=3/
  ]
| #U0 #T1 #HL0 #HT0 #H1 #X2 #l #H2 #X3 #H3 #L2 #HL12 destruct -IH3 -IH2
  elim (snv_inv_cast … H1) -H1 #T0 #l0 #_ #HT1 #HT10 #_
  lapply (ssta_inv_cast1 … H2) -H2 #HTU1
  elim (ssta_mono … HT10 … HTU1) -HT10 #H1 #H2 destruct
  elim (cpr_inv_cast1 … H3) -H3
  [ * #U2 #T2 #_ #HT12 #H destruct
    elim (IH1 … HTU1 … HT12 … HL12) -IH1 -HTU1 -HL12 // [2: /2 width=1/ ] -T1 -U0 /3 width=3/
  | #HT1X3
    elim (IH1 … HTU1 … HT1X3 … HL12) -IH1 -HTU1 -HL12 // [2: /2 width=1/ ] -U0 -T1 /2 width=3/
  ]
]
qed-.
