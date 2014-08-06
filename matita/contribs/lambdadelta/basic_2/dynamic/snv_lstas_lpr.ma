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

include "basic_2/dynamic/snv_aaa.ma".
include "basic_2/dynamic/snv_scpes.ma".
include "basic_2/dynamic/lsubsv_lstas.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

(* Properties on sn parallel reduction for local environments ***************)

fact lstas_cpr_lpr_aux: ∀h,g,G0,L0,T0.
                        (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_snv_lstas h g G1 L1 T1) →
                        (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_snv_cpr_lpr h g G1 L1 T1) →
                        (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_da_cpr_lpr h g G1 L1 T1) →
                        (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_lstas_cpr_lpr h g G1 L1 T1) →
                        ∀G1,L1,T1. G0 = G1 → L0 = L1 → T0 = T1 → IH_lstas_cpr_lpr h g G1 L1 T1.
#h #g #G0 #L0 #T0 #IH4 #IH3 #IH2 #IH1 #G1 #L1 * * [|||| * ]
[ #k #_ #_ #_ #_ #l1 #l2 #_ #_ #X2 #H2 #X3 #H3 #L2 #_ -IH4 -IH3 -IH2 -IH1
  >(lstas_inv_sort1 … H2) -X2
  >(cpr_inv_sort1 … H3) -X3 /2 width=3 by ex2_intro/
| #i #HG0 #HL0 #HT0 #H1 #l1 #l2 @(nat_ind_plus … l2) -l2 [ #_ | #l2 #_ #Hl21 ] #Hl1 #X2 #H2 #X3 #H3 #L2 #HL12 destruct -IH4 -IH3
  [ lapply (lstas_inv_O … H2) -H2 #H destruct -IH1 -H1 -l1 /4 width=5 by lpr_cpcs_conf, cpr_cpcs_dx, ex2_intro/ ]
  elim (snv_inv_lref … H1) -H1 #I0 #K0 #X0 #HK0 #HX0
  elim (da_inv_lref … Hl1) -Hl1 * #K1 [ #V1 | #W1 #l0 ] #HLK1 [ #HVl1 | #HWl1 #H destruct ]
  lapply (drop_mono … HK0 … HLK1) -HK0 #H destruct
  elim (lstas_inv_lref1 … H2) -H2 * #K0 #V0 #W0 [2,4: #X0 ] #HK0 [1,2: #_ -X0 ] #HVW0 #HX2
  lapply (drop_mono … HK0 … HLK1) -HK0 #H destruct
  [ lapply (le_plus_to_le_r … Hl21) -Hl21 #Hl21 ]
  lapply (fqup_lref … G1 … HLK1) #HKV1
  elim (lpr_drop_conf … HLK1 … HL12) -HL12 #X #H #HLK2
  elim (lpr_inv_pair1 … H) -H #K2 [ #W2 | #V2 ] #HK12 [ #HW12 | #HV12 ] #H destruct
  lapply (drop_fwd_drop2 … HLK2) #H2
  elim (cpr_inv_lref1 … H3) -H3
  [1,3: #H destruct -HLK1
  |2,4: * #K0 #V0 #X0 #H #HVX0 #HX0
        lapply (drop_mono … H … HLK1) -H -HLK1 #H destruct
  ]
  [ lapply (IH2 … HWl1 … HW12 … HK12) /2 width=1 by fqup_fpbg/ -IH2 #H
    elim (da_inv_sta … H) -H
    elim (IH1 … HWl1 … HVW0 … HW12 … HK12) -IH1 -HVW0 /2 width=1 by fqup_fpbg/ #V2 #HWV2 #HV2
    elim (lift_total V2 0 (i+1))
    /3 width=12 by cpcs_lift, lstas_ldec, ex2_intro/
  | elim (IH1 … HVl1 … HVW0 … HV12 … HK12) -IH1 -HVl1 -HVW0 -HV12 -HK12 -IH2 /2 width=1 by fqup_fpbg/ #W2 #HVW2 #HW02
    elim (lift_total W2 0 (i+1))
    /4 width=12 by cpcs_lift, lstas_ldef, ex2_intro/
  | elim (IH1 … HVl1 … HVW0 … HVX0 … HK12) -IH1 -HVl1 -HVW0 -HVX0 -HK12 -IH2 -V2 /2 width=1 by fqup_fpbg/ -l1 #W2 #HXW2 #HW02
    elim (lift_total W2 0 (i+1))
    /3 width=12 by cpcs_lift, lstas_lift, ex2_intro/
  ]
| #p #_ #_ #HT0 #H1 destruct -IH4 -IH3 -IH2 -IH1
  elim (snv_inv_gref … H1)
| #a #I #V1 #T1 #HG0 #HL0 #HT0 #H1 #l1 #l2 #Hl21 #Hl1 #X2 #H2 #X3 #H3 #L2 #HL12 destruct -IH4 -IH3 -IH2
  elim (snv_inv_bind … H1) -H1 #_ #HT1
  lapply (da_inv_bind … Hl1) -Hl1 #Hl1
  elim (lstas_inv_bind1 … H2) -H2 #U1 #HTU1 #H destruct
  elim (cpr_inv_bind1 … H3) -H3 *
  [ #V2 #T2 #HV12 #HT12 #H destruct
    elim (IH1 … Hl1 … HTU1 … HT12 (L2.ⓑ{I}V2)) -IH1 -Hl1 -HTU1 -HT12 /2 width=1 by fqup_fpbg, lpr_pair/ -T1
    /4 width=5 by cpcs_bind2, lpr_cpr_conf, lstas_bind, ex2_intro/
  | #T3 #HT13 #HXT3 #H1 #H2 destruct
    elim (IH1 … Hl1 … HTU1 … HT13 (L2.ⓓV1)) -IH1 -Hl1 -HTU1 -HT13 /2 width=1 by fqup_fpbg, lpr_pair/ -T1 -HL12 #U3 #HTU3 #HU13
    elim (lstas_inv_lift1 … HTU3 L2 … HXT3) -T3
    /5 width=8 by cpcs_cpr_strap1, cpcs_bind1, cpr_zeta, drop_drop, ex2_intro/
  ]
| #V1 #T1 #HG0 #HL0 #HT0 #H1 #l1 #l2 #Hl21 #Hl1 #X2 #H2 #X3 #H3 #L2 #HL12 destruct
  elim (snv_inv_appl … H1) -H1 #a #W1 #U1 #l0 #HV1 #HT1 #HVW1 #HTU1
  lapply (da_inv_flat … Hl1) -Hl1 #Hl1
  elim (lstas_inv_appl1 … H2) -H2 #X #HT1U #H destruct
  elim (cpr_inv_appl1 … H3) -H3 *
  [ #V2 #T2 #HV12 #HT12 #H destruct -a -l0 -W1 -U1 -HV1 -IH4 -IH3 -IH2
    elim (IH1 … Hl1 … HT1U … HT12 … HL12) -IH1 -Hl1 -HT1U
    /4 width=5 by fqup_fpbg, cpcs_flat, lpr_cpr_conf, lstas_appl, ex2_intro/
  | #b #V2 #W2 #W3 #T2 #T3 #HV12 #HW23 #HT23 #H1 #H2 destruct
    elim (snv_inv_bind … HT1) -HT1 #HW2 #HT2
    lapply (da_inv_bind … Hl1) -Hl1 #Hl1
    elim (lstas_inv_bind1 … HT1U) -HT1U #U #HT2U #H destruct
    elim (scpds_inv_abst1 … HTU1) -HTU1 #W0 #U0 #HW20 #_ #H destruct -U0 -l0
    elim (snv_fwd_da … HW2) #l0 #HW2l
    lapply (scpds_div … W2 … 0 … HVW1) /2 width=3 by cprs_scpds/ -W0 #H21
    elim (snv_fwd_da … HV1) #l #HV1l
    elim (da_scpes_aux … IH4 IH3 IH2 … HW2l … HV1l … H21) /2 width=1 by fqup_fpbg/ #_ #H
    <minus_n_O #H0 destruct >(plus_minus_m_m l 1) in HV1l; // -H #HV1l
    lapply (scpes_cpr_lpr_aux … IH2 IH1 … H21 … HW23 … HV12 … HL12) -H21 /2 width=1 by fqup_fpbg/ #H32
    lapply (IH3 … HW23 … HL12) /2 width=1 by fqup_fpbg/ #HW3
    lapply (IH3 … HV12 … HL12) /2 width=1 by fqup_fpbg/ #HV2
    lapply (IH2 … HW2l … HW23 … HL12) /2 width=1 by fqup_fpbg/ -HW2 -HW2l #HW3l
    lapply (IH2 … HV1l … HV12 … HL12) /2 width=1 by fqup_fpbg/ -HV1 -HV1l #HV2l
    elim (IH1 … Hl1 … HT2U … HT23 (L2.ⓛW3)) -HT2U /2 width=1 by fqup_fpbg, lpr_pair/ #U3 #HTU3 #HU23
    elim (lsubsv_lstas_trans … g … HTU3 … Hl21 … (L2.ⓓⓝW3.V2)) -HTU3
    [ #U4 #HT3U4 #HU43 -IH1 -IH2 -IH3 -IH4 -l -l1 -HW3 -HV2 -HT2
      @(ex2_intro … (ⓓ{b}ⓝW3.V2.U4)) /2 width=1 by lstas_bind/ -HT3U4
      @(cpcs_canc_dx … (ⓓ{b}ⓝW3.V2.U3)) /2 width=1 by cpcs_bind_dx/ -HU43
      @(cpcs_cpr_strap1 … (ⓐV2.ⓛ{b}W3.U3)) /2 width=1 by cpr_beta/
      /4 width=3 by cpcs_flat, cpcs_bind2, lpr_cpr_conf/
    | -U3
      @(lsubsv_beta … (l-1)) /3 width=7 by fqup_fpbg/
      @shnv_cast [1,2: // ] #l0 #Hl0
      lapply (scpes_le_aux … IH4 IH3 IH2 IH1 … HW3l … HV2l … l0 … H32) -IH4 -IH3 -IH2 -IH1 -HW3l -HV2l -H32
      /3 width=5 by fpbg_fpbs_trans, fqup_fpbg, cpr_lpr_fpbs, le_S_S/
    | -IH1 -IH3 -IH4 /3 width=9 by fqup_fpbg, lpr_pair/
    ]
  | #b #V0 #V2 #W0 #W2 #T0 #T2 #HV10 #HV02 #HW02 #HT02 #H1 #H2 destruct -a -l0 -W1 -HV1 -IH4 -IH3 -IH2
    elim (snv_inv_bind … HT1) -HT1 #_ #HT0
    lapply (da_inv_bind … Hl1) -Hl1 #Hl1
    elim (lstas_inv_bind1 … HT1U) -HT1U #U0 #HTU0 #H destruct
    elim (IH1 … Hl1 … HTU0 … HT02 (L2.ⓓW2)) -IH1 -Hl1 -HTU0 /2 width=1 by fqup_fpbg, lpr_pair/ -T0 #U2 #HTU2 #HU02
    lapply (lpr_cpr_conf … HL12 … HV10) -HV10 #HV10
    lapply (lpr_cpr_conf … HL12 … HW02) -L1 #HW02
    lapply (cpcs_bind2 b … HW02 … HU02) -HW02 -HU02 #HU02
    lapply (cpcs_flat … HV10 … HU02 Appl) -HV10 -HU02 #HU02
    lapply (cpcs_cpr_strap1 … HU02 (ⓓ{b}W2.ⓐV2.U2) ?)
    /4 width=3 by lstas_appl, lstas_bind, cpr_theta, ex2_intro/
  ]
| #W1 #T1 #HG0 #HL0 #HT0 #H1 #l1 #l2 @(nat_ind_plus … l2) -l2 [ #_ | #l2 #_ #Hl21 ] #Hl1 #X2 #H2 #X3 #H3 #L2 #HL12 destruct -IH4 -IH3 -IH2
  [ lapply (lstas_inv_O … H2) -H2 #H destruct -IH1 -H1 -l1 /4 width=5 by lpr_cpcs_conf, cpr_cpcs_dx, ex2_intro/ ]
  elim (snv_inv_cast … H1) -H1 #U1 #_ #HT1 #_ #_ -U1
  lapply (da_inv_flat … Hl1) -Hl1 #Hl1
  lapply (lstas_inv_cast1 … H2) -H2 #HTU1
  elim (cpr_inv_cast1 … H3) -H3
  [ * #U2 #T2 #_ #HT12 #H destruct
    elim (IH1 … Hl1 … HTU1 … HT12 … HL12) -IH1 -Hl1 -HTU1 -HL12
    /3 width=3 by fqup_fpbg, lstas_cast, ex2_intro/
  | #HT1X3 elim (IH1 … Hl1 … HTU1 … HT1X3 … HL12) -IH1 -Hl1 -HTU1 -HL12
    /2 width=3 by fqup_fpbg, ex2_intro/
  ]
]
qed-.
