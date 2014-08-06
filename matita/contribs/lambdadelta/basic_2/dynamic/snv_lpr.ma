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

include "basic_2/dynamic/snv_lift.ma".
include "basic_2/dynamic/snv_aaa.ma".
include "basic_2/dynamic/snv_scpes.ma".
include "basic_2/dynamic/lsubsv_snv.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

(* Properties on context-free parallel reduction for local environments *****)

fact snv_cpr_lpr_aux: ∀h,g,G0,L0,T0.
                      (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_snv_lstas h g G1 L1 T1) →
                      (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_lstas_cpr_lpr h g G1 L1 T1) →
                      (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_da_cpr_lpr h g G1 L1 T1) →
                      (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_snv_cpr_lpr h g G1 L1 T1) →
                      ∀G1,L1,T1. G0 = G1 → L0 = L1 → T0 = T1 → IH_snv_cpr_lpr h g G1 L1 T1.
#h #g #G0 #L0 #T0 #IH4 #IH3 #IH2 #IH1 #G1 #L1 * * [|||| * ]
[ #k #HG0 #HL0 #HT0 #H1 #X #H2 #L2 #_ destruct -IH4 -IH3 -IH2 -IH1 -H1
  >(cpr_inv_sort1 … H2) -X //
| #i #HG0 #HL0 #HT0 #H1 #X #H2 #L2 #HL12 destruct -IH4 -IH3 -IH2
  elim (snv_inv_lref … H1) -H1 #I #K1 #V1 #HLK1 #HV1
  elim (lpr_drop_conf … HLK1 … HL12) -HL12 #X #H #HLK2
  elim (lpr_inv_pair1 … H) -H #K2 #V2 #HK12 #HV12 #H destruct
  lapply (fqup_lref … G1 … HLK1) #HKL
  elim (cpr_inv_lref1 … H2) -H2
  [ #H destruct -HLK1 /4 width=10 by fqup_fpbg, snv_lref/
  | * #K0 #V0 #W0 #H #HVW0 #W0 -HV12
    lapply (drop_mono … H … HLK1) -HLK1 -H #H destruct
    lapply (drop_fwd_drop2 … HLK2) -HLK2 /4 width=8 by fqup_fpbg, snv_lift/
  ]
| #p #HG0 #HL0 #HT0 #H1 #X #H2 #L2 #HL12 destruct -IH4 -IH3 -IH2 -IH1
  elim (snv_inv_gref … H1)
| #a #I #V1 #T1 #HG0 #HL0 #HT0 #H1 #X #H2 #L2 #HL12 destruct -IH4 -IH3 -IH2
  elim (snv_inv_bind … H1) -H1 #HV1 #HT1
  elim (cpr_inv_bind1 … H2) -H2 *
  [ #V2 #T2 #HV12 #HT12 #H destruct /4 width=8 by fqup_fpbg, snv_bind, lpr_pair/
  | #T2 #HT12 #HXT2 #H1 #H2 destruct -HV1
    /4 width=10 by fqup_fpbg, snv_inv_lift, lpr_pair, drop_drop/
  ]
| #V1 #T1 #HG0 #HL0 #HT0 #H1 #X #H2 #L2 #HL12 destruct
  elim (snv_inv_appl … H1) -H1 #a #W1 #U1 #l0 #HV1 #HT1 #HVW1 #HTU1
  elim (cpr_inv_appl1 … H2) -H2 *
  [ #V2 #T2 #HV12 #HT12 #H destruct -IH4
    lapply (IH1 … HV12 … HL12) /2 width=1 by fqup_fpbg/ #HV2
    lapply (IH1 … HT12 … HL12) /2 width=1 by fqup_fpbg/ #HT2
    elim (scpds_cpr_lpr_aux … IH2 IH3 … HVW1 … HV12 … HL12) /2 width=1 by fqup_fpbg/ -HVW1 -HV12 #XV #HVW2 #HXV
    elim (scpds_cpr_lpr_aux … IH2 IH3 … HTU1 … HT12 … HL12) /2 width=1 by fqup_fpbg/ -HTU1 -HT12 #X #HTU2 #H
    elim (cprs_inv_abst1 … H) -H #XW #U2 #HXW #_ #H destruct -IH1 -IH3 -IH2 -L1
    elim (cprs_conf … HXV … HXW) -W1 #W2 #HXV #HXW
    lapply (scpds_cprs_trans … HVW2 … HXV) -XV
    lapply (scpds_cprs_trans … (ⓛ{a}W2.U2) … HTU2 ?)
    /2 width=7 by snv_appl, cprs_bind/
  | #b #V2 #W10 #W20 #T10 #T20 #HV12 #HW120 #HT120 #H1 #H2 destruct
    elim (snv_inv_bind … HT1) -HT1 #HW10 #HT10
    elim (scpds_inv_abst1 … HTU1) -HTU1 #W30 #T30 #HW130 #_ #H destruct -T30 -l0
    elim (snv_fwd_da … HV1) #l #HV1l
    elim (snv_fwd_da … HW10) #l0 #HW10l
    lapply (scpds_div … W10 … 0 … HVW1) /2 width=2 by cprs_scpds/ -W30 #HVW10
    elim (da_scpes_aux … IH4 IH1 IH2 … HW10l … HV1l … HVW10) /2 width=1 by fqup_fpbg/
    #_ #Hl <minus_n_O #H destruct >(plus_minus_m_m l 1) in HV1l; // -Hl #HV1l
    lapply (scpes_cpr_lpr_aux … IH2 IH3 … HVW10 … HW120 … HV12 … HL12) /2 width=1 by fqup_fpbg/ -HVW10 #HVW20
    lapply (IH2 … HV1l … HV12 … HL12) /2 width=1 by fqup_fpbg/ -HV1l #HV2l
    lapply (IH2 … HW10l … HW120 … HL12) /2 width=1 by fqup_fpbg/ -HW10l #HW20l
    lapply (IH1 … HV12 … HL12) /2 width=1 by fqup_fpbg/ #HV2
    lapply (IH1 … HW120 … HL12) /2 width=1 by fqup_fpbg/ -HW10 #HW20
    lapply (IH1 … HT10 … HT120 … (L2.ⓛW20) ?) /2 width=1 by fqup_fpbg, lpr_pair/ -HT10 #HT20
    @snv_bind /2 width=1 by snv_cast_scpes/
    @(lsubsv_snv_trans … HT20) -HT20
    @(lsubsv_beta … (l-1)) //
    @shnv_cast [1,2: // ] #l0 #Hl0
    lapply (scpes_le_aux … IH4 IH1 IH2 IH3 … HW20l … HV2l … l0 … HVW20) -IH4 -IH3 -IH2 -IH1 -HW20l -HV2l -HVW20
    /3 width=5 by fpbg_fpbs_trans, fqup_fpbg, cpr_lpr_fpbs, le_S_S/
  | #b #V0 #V2 #W0 #W2 #T0 #T2 #HV10 #HV02 #HW02 #HT02 #H1 #H2 destruct -IH4
    elim (snv_inv_bind … HT1) -HT1 #HW0 #HT0
    elim (scpds_inv_abbr_abst … HTU1) -HTU1 #X #HTU0 #HX #H destruct
    elim (lift_inv_bind1 … HX) -HX #W3 #U3 #HW13 #_ #H destruct
    elim (scpds_cpr_lpr_aux … IH2 IH3 … HVW1 … HV10 … HL12) /2 width=1 by fqup_fpbg/ -HVW1 #XV #HXV0 #HXVW1
    elim (scpds_cpr_lpr_aux … IH2 IH3 … HTU0 … HT02 (L2.ⓓW2)) /2 width=1 by fqup_fpbg, lpr_pair/ -HTU0 #X #HXT2 #H
    elim (cprs_inv_abst1 … H) -H #W #U2 #HW3 #_ #H destruct -U3
    lapply (IH1 … HW02 … HL12) /2 width=1 by fqup_fpbg/ #HW2
    lapply (IH1 … HV10 … HL12) /2 width=1 by fqup_fpbg/ #HV0
    lapply (IH1 … HT02 (L2.ⓓW2) ?) /2 width=1 by fqup_fpbg, lpr_pair/ -L1 #HT2
    lapply (snv_lift … HV0 (L2.ⓓW2) (Ⓕ) … HV02) /2 width=1 by drop_drop/ -HV0 #HV2
    elim (lift_total XV 0 1) #XW #HXVW
    lapply (scpds_lift … HXV0 (L2.ⓓW2) (Ⓕ) … HV02 … HXVW) /2 width=1 by drop_drop/ -V0 #HXWV2
    lapply (cprs_lift … HXVW1 (L2.ⓓW2) (Ⓕ) … HW13 … HXVW) /2 width=1 by drop_drop/ -W1 -XV #HXW3
    elim (cprs_conf … HXW3 … HW3) -W3 #W3 #HXW3 #HW3
    lapply (scpds_cprs_trans … HXWV2 … HXW3) -XW
    lapply (scpds_cprs_trans … (ⓛ{a}W3.U2) … HXT2 ?) /2 width=1 by cprs_bind/ -W
    /3 width=6 by snv_appl, snv_bind/
  ]
| #W1 #T1 #HG0 #HL0 #HT0 #H1 #X #H2 #L2 #HL12 destruct -IH4
  elim (snv_inv_cast … H1) -H1 #U1 #HW1 #HT1 #HWU1 #HTU1
  elim (cpr_inv_cast1 … H2) -H2
  [ * #W2 #T2 #HW12 #HT12 #H destruct
    elim (snv_fwd_da … HW1) #l #HW1l
    lapply (scpds_div … W1 … 0 … HTU1) /2 width=2 by cprs_scpds/ -U1 -l #HWT1
    lapply (scpes_cpr_lpr_aux … IH2 IH3 … HWT1 … HW12 … HT12 … HL12) /2 width=1 by fqup_fpbg/
    lapply (IH1 … HW12 … HL12) /2 width=1 by fqup_fpbg/
    lapply (IH1 … HT12 … HL12) /2 width=1 by fqup_fpbg/ -L1
    /2 width=1 by snv_cast_scpes/
  | #H -IH3 -IH2 -HW1 -U1
    lapply (IH1 … H … HL12) /2 width=1 by fqup_fpbg/
  ]
]
qed-.
