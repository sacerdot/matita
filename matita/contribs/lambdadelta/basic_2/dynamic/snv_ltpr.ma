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

include "basic_2/computation/dxprs_dxprs.ma".
include "basic_2/dynamic/snv_cpcs.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

(* Properties on context-free parallel reduction for local environments *****)

fact snv_ltpr_tpr_aux: ∀h,g,L0,T0.
                       (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_snv_lsubsv h g L1 T1) →
                       (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_ssta_ltpr_tpr h g L1 T1) →
                       (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_snv_ssta h g L1 T1) →
                       (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_snv_ltpr_tpr h g L1 T1) →
                       ∀L1,T1. L0 = L1 → T0 = T1 → IH_snv_ltpr_tpr h g L1 T1.
#h #g #L0 #T0 #IH4 #IH3 #IH2 #IH1 #L1 * * [||||*]
[ #k #HL0 #HT0 #H1 #L2 #_ #X #H2 destruct -IH4 -IH3 -IH2 -IH1 -L1
  >(tpr_inv_atom1 … H2) -X //
| #i #HL0 #HT0 #H1 #L2 #HL12 #X #H2 destruct -IH4 -IH3 -IH2
  elim (snv_inv_lref … H1) -H1 #I #K1 #V1 #HLK1 #HV1
  >(tpr_inv_atom1 … H2) -X
  elim (ltpr_ldrop_conf … HLK1 … HL12) -HL12 #X #H #HLK2
  elim (ltpr_inv_pair1 … H) -H #K2 #V2 #HK12 #HV12 #H destruct
  lapply (ldrop_pair2_fwd_fw … HLK1 (#i)) -HLK1 #HLK1
  lapply (IH1 … HK12 … HV12) -IH1 -HV12 -HK12 // -HV1 [ /2 width=1/ ] -HLK1 /2 width=5/
| #p #HL0 #HT0 #H1 #L2 #HL12 #X #H2 destruct -IH4 -IH3 -IH2 -IH1
  elim (snv_inv_gref … H1)
| #a #I #V1 #T1 #HL0 #HT0 #H1 #L2 #HL12 #X #H2 destruct -IH4 -IH3 -IH2
  elim (snv_inv_bind … H1) -H1 #HV1 #HT1
  elim (tpr_inv_bind1 … H2) -H2 *
  [ #V2 #T0 #T2 #HV12 #HT10 #HT02 #H destruct
    lapply (tps_lsubr_trans … HT02 (L2.ⓑ{I}V2) ?) -HT02 /2 width=1/ #HT02
    lapply (IH1 … HL12 … HV12) // [ /2 width=1/ ] #HV2
    lapply (snv_ltpr_cpr_aux … HT1  (L2.ⓑ{I}V2) … T2 ?) -HT1
    [ /3 width=5 by cpr_intro, tps_tpss/ | /2 width=1/ | /3 width=1/ ] -IH1 -T0 /2 width=1/
  | #T2 #HT12 #HXT2 #H1 #H2 destruct
    lapply (IH1 … HT1 (L2.ⓓV1) … HT12) -IH1 -HT1 -HT12 [1,2: /2 width=1/ ] -HL12 #HT2
    lapply (snv_inv_lift … HT2 L2 … HXT2) -T2 // /2 width=1/
  ]
| #V1 #T1 #HL0 #HT0 #H1 #L2 #HL12 #X #H2 destruct
  elim (snv_inv_appl … H1) -H1 #a #W10 #W1 #U1 #l #HV1 #HT1 #HVW1 #HW10 #HTU1
  elim (tpr_inv_appl1 … H2) -H2 *
  [ #V2 #T2 #HV12 #HT12 #H destruct -IH4
    lapply (IH1 … HV1 … HL12 … HV12) [ /2 width=1/ ] #HV2
    lapply (IH1 … HT1 … HL12 … HT12) [ /2 width=1/ ] #HT2
    elim (IH3 … HVW1 … HL12 … HV12) -HVW1 -HV12 // -HV1 [2: /2 width=1/ ] #W2 #HVW2 #HW12
    elim (dxprs_ltpr_cprs_aux … IH2 IH1 IH3 … HTU1 … HL12 T2) // [2: /3 width=1/ |3: /2 width=1/ ] -IH2 -IH1 -IH3 -HT1 -HT12 -HTU1 #X #HTU2 #H
    elim (cprs_inv_abst1 Abst W1 … H) -H #W20 #U2 #HW120 #_ #H destruct
    lapply (ltpr_cprs_conf … HL12 … HW10) -L1 #HW10
    lapply (cpcs_cprs_strap1 … HW10 … HW120) -W1 #HW120
    lapply (cpcs_canc_sn … HW12 HW120) -W10 #HW20
    elim (cpcs_inv_cprs … HW20) -HW20 #W0 #HW20 #HW200
    lapply (dxprs_cprs_trans … (ⓛ{a}W0.U2) HTU2 ?) [ /2 width=1/ ] -HW200 -HTU2 /2 width=8/
  | #b #V2 #W20 #T20 #T2 #HV12 #HT202 #H1 #H2 destruct
    elim (snv_inv_bind … HT1) -HT1 #HW20 #HT20
    elim (dxprs_inv_abst1 … HTU1) -HTU1 #W30 #T30 #HW230 #_ #H destruct -T30
    lapply (cprs_div … HW10 … HW230) -W30 #HW120
    elim (snv_fwd_ssta … HW20) #l0 #U20 #HWU20
    elim (ssta_fwd_correct … HVW1) <minus_plus_m_m #U10 #HWU10
    elim (ssta_ltpr_cpcs_aux … IH1 IH3 … HW20 … HWU10 … HWU20) // -IH3 -HWU10
    [2: /3 width=5/ |3: /2 width=1/
    |4: /4 width=4 by ygt_yprs_trans, ypr_yprs, ypr_ssta, fw_ygt/
    ] #H #_ -IH2 -U10 destruct
    lapply (IH4 … HT20 (L1.ⓓV1) ?) [ /2 width=6/ | /2 width=1/ ] -U20 -W10 -l0 -IH4 -HT20 -HW20 #HT20
    lapply (IH1 … HL12 … HV12) // [ /2 width=1/ ] #HV2
    lapply (IH1 … HT20 … (L2.ⓓV2) … HT202) [1,2: /2 width=1/ ] -L1 -V1 -W20 -T20 /2 width=1/
  | #b #V0 #V2 #W0 #W2 #T0 #T2 #HV10 #HW02 #HT02 #HV02 #H1 #H2 destruct -IH4
    elim (snv_inv_bind … HT1) -HT1 #HW0 #HT0
    elim (dxprs_inv_abbr_abst … HTU1) -HTU1 #X #HTU0 #HX #H destruct
    elim (lift_inv_bind1 … HX) -HX #W3 #U3 #HW13 #_ #H destruct
    lapply (ltpr_cprs_conf … HL12 … HW10) -HW10 #HW10
    elim (dxprs_ltpr_cprs_aux … IH2 IH1 IH3 … HTU0 (L2.ⓓW2) … T2 ?) // [2: /3 width=1/ |3,4: /2 width=1/ ] -IH2 -HTU0 #X #HTU2 #H
    elim (cprs_inv_abst1 Abst W3 … H) -H #W #U2 #HW1 #_ #H destruct -U3
    elim (IH3 … HVW1 … HL12 … HV10) // /2 width=1/ -IH3 -HVW1 #X #H1 #H2
    lapply (cpcs_canc_sn … H2 HW10) -W10 #H2
    elim (lift_total X 0 1) #W20 #H3
    lapply (ssta_lift … H1 (L2.ⓓW2) … HV02 … H3) /2 width=1/ -H1 #HVW20
    lapply (cpcs_lift (L2.ⓓW2) … H3 … HW13 H2) /2 width=1/ -HW13 -H3 -H2 #HW320
    lapply (cpcs_cprs_strap1 … HW320 … HW1) -W3 #HW20
    elim (cpcs_inv_cprs … HW20) -HW20 #W3 #HW203 #HW3
    lapply (dxprs_cprs_trans … (ⓛ{a}W3.U2) HTU2 ?) [ /2 width=1/ ] -HW3 -HTU2 #HTU2
    lapply (IH1 … HL12 … HW02) // [ /2 width=1/ ] -HW0 #HW2
    lapply (IH1 … HL12 … HV10) // [ /2 width=1/ ] -HV1 -HV10 #HV0
    lapply (IH1 … HT0 … (L2.ⓓW2) … HT02) [1,2: /2 width=1/ ] -L1 -HT02 -HW02 #HT2
    lapply (snv_lift … HV0 (L2.ⓓW2) … HV02) /2 width=1/ -HV0 -HV02 /3 width=8/
  ]
| #W1 #T1 #HL0 #HT0 #H1 #L2 #HL12 #X #H2 destruct -IH4 -IH2
  elim (snv_inv_cast … H1) -H1 #U1 #l #HW1 #HT1 #HTU1 #HUW1
  elim (tpr_inv_cast1 … H2) -H2
  [ * #W2 #T2 #HW12 #HT12 #H destruct
    lapply (cpcs_cprs_strap1 … HUW1 W2 ?) [ /3 width=1/ ] -HUW1 #H1
    lapply (IH1 … HL12 … HW12) // /2 width=1/ -HW1 -HW12 #HW2
    lapply (IH1 … HL12 … HT12) // /2 width=1/ -IH1 #HT2
    elim (IH3 … HTU1 … HL12 … HT12) // /2 width=1/ -IH3 -HT1 -HT12 -HTU1 #U2 #HTU2 #HU12
    lapply (ltpr_cpcs_conf … HL12 … H1) -L1 #H1
    lapply (cpcs_canc_sn … HU12 H1) -U1 /2 width=4/
  | #H -IH3 -HW1 -HTU1 -HUW1
    lapply (IH1 … HL12 … H) // /2 width=1/
  ]
]  
qed-.
