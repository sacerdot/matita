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

include "ground_2/lib/arith_2b.ma".
include "basic_2/rt_computation/cprs_cprs.ma".
include "basic_2/dynamic/cnv_drops.ma".
include "basic_2/dynamic/cnv_preserve_sub.ma".
include "basic_2/dynamic/cnv_aaa.ma".
include "basic_2/dynamic/lsubv_cnv.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

(* Sub preservation propery with t-bound rt-transition for terms ************)

fact cnv_cpm_trans_lpr_aux (h) (a):
     ∀G0,L0,T0.
     (∀G1,L1,T1. ⦃G0,L0,T0⦄ >[h] ⦃G1,L1,T1⦄ → IH_cnv_cpms_conf_lpr h a G1 L1 T1) →
     (∀G1,L1,T1. ⦃G0,L0,T0⦄ >[h] ⦃G1,L1,T1⦄ → IH_cnv_cpm_trans_lpr h a G1 L1 T1) →
     ∀G1,L1,T1. G0 = G1 → L0 = L1 → T0 = T1 → IH_cnv_cpm_trans_lpr h a G1 L1 T1.
#h #a #G0 #L0 #T0 #IH2 #IH1 #G1 #L1 * * [|||| * ]
[ #s #HG0 #HL0 #HT0 #H1 #x #X #H2 #L2 #_ destruct -IH2 -IH1 -H1
  elim (cpm_inv_sort1 … H2) -H2 #H #_ destruct //
| #i #HG0 #HL0 #HT0 #H1 #x #X #H2 #L2 #HL12 destruct -IH2
  elim (cnv_inv_lref_drops … H1) -H1 #I #K1 #V1 #HLK1 #HV1
  elim (lpr_drops_conf … HLK1 … HL12) -HL12 // #Y #H #HLK2
  elim (lpr_inv_pair_sn … H) -H #K2 #V2 #HK12 #HV12 #H destruct
  lapply (fqup_lref (Ⓣ) … G1 … HLK1) #HKL
  elim (cpm_inv_lref1_drops … H2) -H2 *
  [ #H1 #H2 destruct -HLK1 /4 width=7 by fqup_fpbg, cnv_lref_drops/
  | #K0 #V0 #W0 #H #HVW0 #W0 -HV12
    lapply (drops_mono … H … HLK1) -HLK1 -H #H destruct
    lapply (drops_isuni_fwd_drop2 … HLK2) -HLK2 /4 width=7 by fqup_fpbg, cnv_lifts/
  | #n #K0 #V0 #W0 #H #HVW0 #W0 #H destruct -HV12
    lapply (drops_mono … H … HLK1) -HLK1 -H #H destruct
    lapply (drops_isuni_fwd_drop2 … HLK2) -HLK2 /4 width=7 by fqup_fpbg, cnv_lifts/
  ]
| #l #HG0 #HL0 #HT0 #H1 #x #X #H2 #L2 #HL12 destruct -IH2 -IH1
  elim (cnv_inv_gref … H1)
| #p #I #V1 #T1 #HG0 #HL0 #HT0 #H1 #x #X #H2 #L2 #HL12 destruct -IH2
  elim (cnv_inv_bind … H1) -H1 #HV1 #HT1
  elim (cpm_inv_bind1 … H2) -H2 *
  [ #V2 #T2 #HV12 #HT12 #H destruct /4 width=9 by fqup_fpbg, cnv_bind, lpr_pair/
  | #X1 #HXT1 #HX1 #H1 #H2 destruct -HV1
    /5 width=7 by cnv_inv_lifts, fqup_fpbg, fqup_zeta, drops_refl, drops_drop/
  ]
| #V1 #T1 #HG0 #HL0 #HT0 #H1 #x #X #H2 #L2 #HL12 destruct
  elim (cnv_inv_appl … H1) -H1 #n #p #W1 #U1 #Hn #HV1 #HT1 #HVW1 #HTU1
  elim (cpm_inv_appl1 … H2) -H2 *
  [ #V2 #T2 #HV12 #HT12 #H destruct
    lapply (IH1 … HV12 … HL12) /2 width=1 by fqup_fpbg/ #HV2
    lapply (IH1 … HT12 … HL12) /2 width=1 by fqup_fpbg/ #HT2
    elim (cnv_cpms_strip_lpr_sub … IH2 … HVW1 … HV12 … HL12 … HL12) [|*: /2 width=2 by fqup_fpbg/ ] -HVW1 -HV12
    <minus_n_O <minus_O_n #XW1 #HXW1 #HXV2
    elim (cnv_cpms_strip_lpr_sub … IH2 … HTU1 … HT12 … HL12 … HL12) [|*: /2 width=2 by fqup_fpbg/ ] -HTU1 -HT12
    #X #H #HTX2 -IH2 -IH1 -L1 -V1 -T1
    elim (cpms_inv_abst_sn … H) -H #W2 #X2 #HW12 #_ #H destruct
    elim (cprs_conf … HXW1 … HW12) -W1 #W1 #HXW1 #HW21
    lapply (cpms_trans … HXV2 … HXW1) -XW1 <plus_n_O #HV2W1
    lapply (cpms_trans … HTX2 … (ⓛ{p}W1.X2) ?)
    [3:|*: /2 width=2 by cpms_bind/ ] -W2 <plus_n_O #HTX2
    elim (cnv_fwd_cpms_abst_dx_le … HT2 … HTX2 n) -HTX2 [| // ] #U2 #HTU2 #_ -X2
    /2 width=7 by cnv_appl/
  | #q #V2 #W10 #W20 #T10 #T20 #HV12 #HW120 #HT120 #H1 #H2 destruct
    elim (cnv_inv_bind … HT1) -HT1 #HW10 #HT10
    elim (cpms_inv_abst_sn … HTU1) -HTU1 #W30 #T30 #HW130 #_ #H destruct -T30
    lapply (IH1 … HV12 … HL12) /2 width=1 by fqup_fpbg/ #HV2
    lapply (IH1 … HW120 … HL12) /2 width=1 by fqup_fpbg/ #HW20
    lapply (IH1 … HT10 … HT120 … (L2.ⓛW20) ?) /2 width=1 by fqup_fpbg, lpr_pair/ -HT10 -HT120 #HT20
    elim (cnv_cpms_strip_lpr_sub … IH2 … HVW1 … HV12 … HL12 … HL12) [|*: /2 width=2 by fqup_fpbg/ ] -HVW1 -HV12
    <minus_n_O <minus_O_n #XW1 #HXW1 #HXV2
    elim (cnv_cpms_strip_lpr_sub … IH2 … HW130 … HW120 … HL12 … HL12) [|*: /2 width=2 by fqup_fpbg/ ] -HW130 -HW120
    <minus_n_O #XW30 #HXW30 #HW230 -IH2 -IH1 -L1 -V1 -W10 -T10
    elim (cprs_conf … HXW1 … HXW30) -W30 #W30 #HXW1 #HXW30
    lapply (cpms_trans … HXV2 … HXW1) -XW1 <plus_n_O #HV2W30
    lapply (cprs_trans … HW230 … HXW30) -XW30 #HW230
    /5 width=4 by lsubv_cnv_trans, lsubv_beta, cnv_cast, cnv_bind/
  | #q #V0 #V2 #W0 #W2 #T0 #T2 #HV10 #HV02 #HW02 #HT02 #H1 #H2 destruct
    elim (cnv_inv_bind … HT1) -HT1 #HW0 #HT0
    elim (cpms_inv_abbr_abst … HTU1) -HTU1 #X #HTU0 #HX #H destruct
    elim (lifts_inv_bind1 … HX) -HX #W3 #U3 #HW13 #_ #H destruct
    lapply (IH1 … HW02 … HL12) /2 width=1 by fqup_fpbg/ #HW2
    lapply (IH1 … HV10 … HL12) /2 width=1 by fqup_fpbg/ #HV0
    lapply (IH1 … HT02 (L2.ⓓW2) ?) /2 width=1 by fqup_fpbg, lpr_pair/ #HT2
    elim (cnv_cpms_strip_lpr_sub … IH2 … HVW1 … HV10 … HL12 … HL12) [|*: /2 width=2 by fqup_fpbg/ ] -HVW1 -HV10
    <minus_n_O <minus_O_n #XW1 #HXW1 #HXV0
    elim (cnv_cpms_strip_lpr_sub … IH2 … HTU0 … HT02 … (L2.ⓓW2) … (L2.ⓓW2)) [|*: /2 width=2 by fqup_fpbg, lpr_pair/ ] -HTU0 -HT02 -HW02
    #X #H #HTX2 -IH2 -IH1 -L1 -W0 -T0 -U1
    elim (cpms_inv_abst_sn … H) -H #W #X2 #HW3 #_ #H destruct -U3
    lapply (cnv_lifts … HV0 (Ⓣ) … (L2.ⓓW2) … HV02) /3 width=1 by drops_refl, drops_drop/ -HV0 #HV2
    elim (cpms_lifts_sn … HXV0 (Ⓣ) … (L2.ⓓW2) … HV02) /3 width=1 by drops_refl, drops_drop/ -V0 #XW2 #HXW12 #HXVW2
    lapply (cpms_lifts_bi … HXW1 (Ⓣ) … (L2.ⓓW2) … HW13 … HXW12) /3 width=1 by drops_refl, drops_drop/ -W1 -XW1 #HXW32
    elim (cprs_conf … HXW32 … HW3) -W3 #W3 #HXW23 #HW3
    lapply (cpms_trans … HXVW2 … HXW23) -XW2 <plus_n_O #H1
    lapply (cpms_trans … HTX2 ? (ⓛ{p}W3.X2) ?) [3:|*:/2 width=2 by cpms_bind/ ] -W #H2
    elim (cnv_fwd_cpms_abst_dx_le … HT2 … H2 n) -H2 [| // ] #U2 #HTU2 #_ -X2
    /3 width=7 by cnv_appl, cnv_bind/
  ]
| #W1 #T1 #HG0 #HL0 #HT0 #H1 #x #X #H2 #L2 #HL12 destruct
  elim (cnv_inv_cast … H1) -H1 #U1 #HW1 #HT1 #HWU1 #HTU1
  elim (cpm_inv_cast1 … H2) -H2
  [ * #W2 #T2 #HW12 #HT12 #H destruct
    lapply (IH1 … HW12 … HL12) /2 width=1 by fqup_fpbg/ #HW2
    lapply (IH1 … HT12 … HL12) /2 width=1 by fqup_fpbg/ #HT2
    lapply (cnv_cpms_trans_lpr_sub … IH1 … HTU1 L1 ?) /2 width=1 by fqup_fpbg/ #HU1
    elim (cnv_cpms_strip_lpr_sub … IH2 … HWU1 … HW12 … L1 … HL12) [|*: /2 width=2 by fqup_fpbg/ ] -HW12
    <minus_n_O <minus_O_n #XW1 #HXUW1 #HXW21
    elim (cnv_cpms_strip_lpr_sub … IH2 … HTU1 … HT12 … L1 … HL12) [|*: /2 width=2 by fqup_fpbg/ ] -HTU1 -HT12
    #XT1 #HXUT1 #HXT21
    elim (IH2 … HXUW1 … HXUT1 … HL12 … HL12) [|*: /2 width=4 by fqup_cpms_fwd_fpbg/ ] -HXUW1 -HXUT1 -HWU1
    >eq_minus_O // #W0 #H1 #H2 -IH2 -IH1 -L1 -W1 -T1 -U1
    lapply (cprs_trans … HXW21 … H1) -XW1 #H1
    lapply (cpms_trans … HXT21 … H2) -XT1 <arith_l1 #H2
    /2 width=3 by cnv_cast/
  | #HX -IH2 -HW1 -U1
    lapply (IH1 … HX … HL12) /2 width=1 by fqup_fpbg/
  | * #n #HX #H destruct -IH2 -HT1 -U1
    lapply (IH1 … HX … HL12) /2 width=1 by fqup_fpbg/
  ]
]
qed-.
