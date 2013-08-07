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
include "basic_2/dynamic/snv_lift.ma".
include "basic_2/dynamic/snv_cpcs.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

(* Properties on context-free parallel reduction for local environments *****)

fact snv_cpr_lpr_aux: ∀h,g,G0,L0,T0.
                      (∀G1,L1,T1. ⦃G0, L0, T0⦄ >[h, g] ⦃G1, L1, T1⦄ → IH_snv_lsubsv h g G1 L1 T1) →
                      (∀G1,L1,T1. ⦃G0, L0, T0⦄ >[h, g] ⦃G1, L1, T1⦄ → IH_ssta_cpr_lpr h g G1 L1 T1) →
                      (∀G1,L1,T1. ⦃G0, L0, T0⦄ >[h, g] ⦃G1, L1, T1⦄ → IH_snv_ssta h g G1 L1 T1) →
                      (∀G1,L1,T1. ⦃G0, L0, T0⦄ >[h, g] ⦃G1, L1, T1⦄ → IH_snv_cpr_lpr h g G1 L1 T1) →
                      ∀G1,L1,T1. G0 = G1 → L0 = L1 → T0 = T1 → IH_snv_cpr_lpr h g G1 L1 T1.
#h #g #G0 #L0 #T0 #IH4 #IH3 #IH2 #IH1 #G1 #L1 * * [||||*]
[ #k #HG0 #HL0 #HT0 #H1 #X #H2 #L2 #_ destruct -IH4 -IH3 -IH2 -IH1 -H1
  >(cpr_inv_sort1 … H2) -X //
| #i #HG0 #HL0 #HT0 #H1 #X #H2 #L2 #HL12 destruct -IH4 -IH3 -IH2
  elim (snv_inv_lref … H1) -H1 #I #K1 #V1 #HLK1 #HV1
  elim (lpr_ldrop_conf … HLK1 … HL12) -HL12 #X #H #HLK2
  elim (lpr_inv_pair1 … H) -H #K2 #V2 #HK12 #HV12 #H destruct
  lapply (fsupp_lref … G1 … HLK1) #HKL
  elim (cpr_inv_lref1 … H2) -H2
  [ #H destruct -HLK1
    lapply (IH1 … HV12 … HK12) -IH1 -HV12 -HK12 // -HV1 [ /2 width=1/ ] -HKL /2 width=5/
  | * #K0 #V0 #W0 #H #HVW0 #W0 -HV12
    lapply (ldrop_mono … H … HLK1) -HLK1 -H #H destruct
    lapply (ldrop_fwd_ldrop2 … HLK2) -HLK2 #HLK2
    lapply (IH1 … HVW0 … HK12) -IH1 -HVW0 -HK12 // -HV1 [ /2 width=1/ ] -HKL /3 width=7/
  ]
| #p #HG0 #HL0 #HT0 #H1 #X #H2 #L2 #HL12 destruct -IH4 -IH3 -IH2 -IH1
  elim (snv_inv_gref … H1)
| #a #I #V1 #T1 #HG0 #HL0 #HT0 #H1 #X #H2 #L2 #HL12 destruct -IH4 -IH3 -IH2
  elim (snv_inv_bind … H1) -H1 #HV1 #HT1
  elim (cpr_inv_bind1 … H2) -H2 *
  [ #V2 #T2 #HV12 #HT12 #H destruct
    lapply (IH1 … HV12 … HL12) // -HV1 [ /2 width=1/ ] #HV2
    lapply (IH1 … HT12  (L2.ⓑ{I}V2) ?) // -IH1 /2 width=1/
  | #T2 #HT12 #HXT2 #H1 #H2 destruct -HV1
    lapply (IH1 … HT1 … HT12 (L2.ⓓV1) ?) -IH1 [1,2: /2 width=1/ ] -L1 -T1 #HT2
    lapply (snv_inv_lift … HT2 L2 … HXT2) -T2 // /2 width=1/
  ]
| #V1 #T1 #HG0 #HL0 #HT0 #H1 #X #H2 #L2 #HL12 destruct
  elim (snv_inv_appl … H1) -H1 #a #W10 #W1 #U1 #l #HV1 #HT1 #HVW1 #HW10 #HTU1
  elim (cpr_inv_appl1 … H2) -H2 *
  [ #V2 #T2 #HV12 #HT12 #H destruct -IH4
    lapply (IH1 … HV1 … HV12 … HL12) [ /2 width=1/ ] #HV2
    lapply (IH1 … HT1 … HT12 … HL12) [ /2 width=1/ ] #HT2
    elim (IH3 … HVW1 … HV12 … HL12) -HVW1 -HV12 // -HV1 [2: /2 width=1/ ] #W2 #HVW2 #HW12
    elim (cpds_cprs_lpr_aux … IH2 IH1 IH3 … HTU1 … T2 … HL12) // [2,3: /2 width=1/ ] -IH2 -IH1 -IH3 -HT1 -HT12 -HTU1 #X #HTU2 #H
    elim (cprs_inv_abst1 … H) -H #W20 #U2 #HW120 #_ #H destruct
    lapply (lpr_cprs_conf … HL12 … HW10) -L1 #HW10
    lapply (cpcs_cprs_strap1 … HW10 … HW120) -W1 #HW120
    lapply (cpcs_canc_sn … HW12 HW120) -W10 #HW20
    elim (cpcs_inv_cprs … HW20) -HW20 #W0 #HW20 #HW200
    lapply (cpds_cprs_trans … (ⓛ{a}W0.U2) HTU2 ?) [ /2 width=1/ ] -HW200 -HTU2 /2 width=8/
  | #b #V2 #W20 #W2 #T20 #T2 #HV12 #HW202 #HT202 #H1 #H2 destruct
    elim (snv_inv_bind … HT1) -HT1 #HW20 #HT20
    elim (cpds_inv_abst1 … HTU1) -HTU1 #W30 #T30 #HW230 #_ #H destruct -T30
    lapply (cprs_div … HW10 … HW230) -W30 #HW120
    lapply (cpcs_cpr_strap1 … HW120 … HW202) -HW120 #HW102
    lapply (lpr_cpcs_conf … HL12 … HW102) -HW102 #HW102
    elim (IH3 … HVW1 … HV12 … HL12) // [2: /2 width=1/ ] -HVW1 #W3 #HV2W3 #HW103
    lapply (cpcs_canc_sn … HW103 … HW102) -W10 #HW32
    lapply (IH1 … HV12 … HL12) // [ /2 width=1/ ] -HV1 #HV2
    lapply (IH1 … HW202 … HL12) // [ /2 width=1/ ] -HW20 #HW2
    lapply (IH1 … HT20 … HT202 … (L2.ⓛW2) ?) [1,2: /2 width=1/ ] -HT20 #HT2
    lapply (IH2 … HV2W3) //
    [ @(ygt_yprs_trans … G1 G1 … L1 L1 … V1) (**) (* auto /4 width=5/ is a bit slow even with trace *)
      [ /2 width=1 by fsupp_ygt/
      | /3 width=1 by cprs_lpr_yprs, cpr_cprs/
      ]
    ] #HW3
    elim (snv_fwd_ssta … HW2) #l0 #U2 #HWU2
    elim (ssta_fwd_correct … HV2W3) <minus_plus_m_m #U3 #HWU3
    elim (ssta_cpcs_lpr_aux … IH1 IH3 … HWU3 … HWU2 … HW32 … L2) // -IH3
    [2: /4 width=5 by ygt_yprs_trans, fsupp_ygt, cprs_lpr_yprs, cpr_cprs/
    |3: @(ygt_yprs_trans … G1 G1 L1 L2 … V2) (**) (* auto not tried *)
        [ @(ygt_yprs_trans … G1 G1 L1 L1 … V1)
          [ /2 width=1 by fsupp_ygt/
          | /3 width=1 by cprs_lpr_yprs, cpr_cprs/
          ]
        | /3 width=2 by ypr_ssta, ypr_yprs/
        ]
    ] #H #_  destruct -IH2 -U3
    lapply (IH4 … HT2 (L2.ⓓⓝW2.V2) ?)
    [ /3 width=5/
    | @(ygt_yprs_trans … G1 G1 … (L1.ⓛW20) … T2) (**) (* auto /5 width=5/ is too slow even with trace timeout=35 *)
      [ /4 width=5 by ygt_yprs_trans, fsupp_ygt, ypr_yprs, ypr_cpr/
      | /4 width=1 by ypr_yprs, ypr_lpr, lpr_pair/
      ]
    ] -L1 -V1 -T20 -U2 /3 width=4/
  | #b #V0 #V2 #W0 #W2 #T0 #T2 #HV10 #HV02 #HW02 #HT02 #H1 #H2 destruct -IH4
    elim (snv_inv_bind … HT1) -HT1 #HW0 #HT0
    elim (cpds_inv_abbr_abst … HTU1) -HTU1 #X #HTU0 #HX #H destruct
    elim (lift_inv_bind1 … HX) -HX #W3 #U3 #HW13 #_ #H destruct
    lapply (lpr_cprs_conf … HL12 … HW10) -HW10 #HW10
    elim (cpds_cprs_lpr_aux … IH2 IH1 IH3 … HTU0 T2 … (L2.ⓓW2)) // [2,3,4: /2 width=1/ ] -IH2 -HTU0 #X #HTU2 #H
    elim (cprs_inv_abst1 … H) -H #W #U2 #HW1 #_ #H destruct -U3
    elim (IH3 … HVW1 … HV10 … HL12) // /2 width=1/ -IH3 -HVW1 #X #H1 #H2
    lapply (cpcs_canc_sn … H2 HW10) -W10 #H2
    elim (lift_total X 0 1) #W20 #H3
    lapply (ssta_lift … H1 (L2.ⓓW2) … HV02 … H3) /2 width=1/ -H1 #HVW20
    lapply (cpcs_lift … (L2.ⓓW2) … H3 … HW13 H2) /2 width=1/ -HW13 -H3 -H2 #HW320
    lapply (cpcs_cprs_strap1 … HW320 … HW1) -W3 #HW20
    elim (cpcs_inv_cprs … HW20) -HW20 #W3 #HW203 #HW3
    lapply (cpds_cprs_trans … (ⓛ{a}W3.U2) HTU2 ?) [ /2 width=1/ ] -HW3 -HTU2 #HTU2
    lapply (IH1 … HW02 … HL12) // [ /2 width=1/ ] -HW0 #HW2
    lapply (IH1 … HV10 … HL12) // [ /2 width=1/ ] -HV1 -HV10 #HV0
    lapply (IH1 … HT02 (L2.ⓓW2) ?) // [1,2: /2 width=1/ ] -L1 #HT2
    lapply (snv_lift … HV0 (L2.ⓓW2) … HV02) /2 width=1/ -HV0 -HV02 /3 width=8/
  ]
| #W1 #T1 #HG0 #HL0 #HT0 #H1 #X #H2 #L2 #HL12 destruct -IH4 -IH2
  elim (snv_inv_cast … H1) -H1 #U1 #l #HW1 #HT1 #HTU1 #HUW1
  elim (cpr_inv_cast1 … H2) -H2
  [ * #W2 #T2 #HW12 #HT12 #H destruct
    lapply (cpcs_cprs_strap1 … HUW1 W2 ?) [ /2 width=1/ ] -HUW1 #H1
    lapply (IH1 … HW12 … HL12) // /2 width=1/ -HW1 -HW12 #HW2
    lapply (IH1 … HT12 … HL12) // /2 width=1/ -IH1 #HT2
    elim (IH3 … HTU1 … HT12 … HL12) // /2 width=1/ -IH3 -HT1 -HT12 -HTU1 #U2 #HTU2 #HU12
    lapply (lpr_cpcs_conf … HL12 … H1) -L1 #H1
    lapply (cpcs_canc_sn … HU12 H1) -U1 /2 width=4/
  | #H -IH3 -HW1 -HTU1 -HUW1
    lapply (IH1 … H … HL12) // /2 width=1/
  ]
]
qed-.
