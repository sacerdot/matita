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


include "basic_2/reducibility/ltpr.ma".
include "basic_2/computation/xprs_lift.ma".
include "basic_2/equivalence/cpcs_cpcs.ma".
include "basic_2/equivalence/lsubse_ssta.ma".
include "basic_2/equivalence/fpcs_cpcs.ma".
include "basic_2/equivalence/fpcs_fpcs.ma".
include "basic_2/dynamic/snv_ssta.ma".
(*
include "basic_2/static/ssta_ltpss_dx.ma".
include "basic_2/dynamic/snv_lift.ma".
*)
(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

(* Properties on context-free parallel reduction for local environments *****)

fact ssta_ltpr_tpr_aux: ∀h,g,n. (
                           ∀L,T2. ♯{L,T2} < n →
                           ∀T1. L ⊢ T1 ⬌* T2 → ⦃h, L⦄ ⊩ T1 :[g] → ⦃h, L⦄ ⊩ T2 :[g] →
                           ∀U1,l1. ⦃h, L⦄ ⊢ T1 •[g, l1] U1 →
                           ∀U2,l2. ⦃h, L⦄ ⊢ T2 •[g, l2] U2 →
                           L ⊢ U1 ⬌* U2 ∧ l1 = l2
                        ) → (
                           ∀L,T. ♯{L,T} < n → ⦃h, L⦄ ⊩ T :[g] →
                           ∀U,l. ⦃h, L⦄ ⊢ T •[g, l + 1] U → ⦃h, L⦄ ⊩ U :[g]
                        ) → (
                           ∀L1,T1. ♯{L1,T1} < n →
                           ∀U1,l. ⦃h, L1⦄ ⊢ T1 •[g, l] U1 →
                           ∀L2. L1 ➡ L2 → ∀T2. T1 ➡ T2 → ⦃h, L1⦄ ⊩ T1 :[g] → 
                           ∃∃U2. ⦃h, L2⦄ ⊢ T2 •[g, l] U2 & ⦃L1, U1⦄ ⬌* ⦃L2, U2⦄
                        ) →
                        ∀L1,T1. ♯{L1,T1} = n →
                        ∀U1,l. ⦃h, L1⦄ ⊢ T1 •[g, l] U1 →
                        ∀L2. L1 ➡ L2 → ∀T2. T1 ➡ T2 → ⦃h, L1⦄ ⊩ T1 :[g] →
                        ∃∃U2. ⦃h, L2⦄ ⊢ T2 •[g, l] U2 & ⦃L1, U1⦄ ⬌* ⦃L2, U2⦄.
#h #g #n #IH3 #IH2 #IH1 #L1 * * [|||| *]
[
|
|
|
| #V1 #T1 #Hn #Y #l #H1 #L2 #HL12 #X #H2 #H3 destruct
  elim (ssta_inv_appl1 … H1) -H1 #U1 #HTU1 #H destruct
  elim (snv_inv_appl … H3) -H3 #a #W1 #W10 #U10 #l0 #HV1 #HT1 #HVW1 #HW10 #HTU10
  elim (tpr_inv_appl1 … H2) -H2 *
  [
  | #b #V2 #W #T2 #T20 #HV12 #HT20 #H1 #H2 destruct
    elim (snv_inv_bind … HT1) -HT1 #HW #HT2
    elim (ssta_inv_bind1 … HTU1) -HTU1 #U2 #HTU2 #H destruct
    elim (xprs_fwd_abst1 … HTU10) -HTU10 #W0 #U0 #HW0 #H destruct
    lapply (cprs_div … HW10 … HW0) -W0 #HW1
    elim (ssta_fwd_correct … HVW1) <minus_plus_m_m #X1 #HWX1
    elim (snv_ssta … HW) #V #l1 #HWV
    elim (IH3 … HW1 … HW … HWX1 … HWV) -IH3 -HWX1 // [2: /2 width=5/ ] -IH2 #_ #H destruct -X1
    elim (IH1 … HVW1 … HL12 … HV12) -HVW1 // -HV1 #W2 #HVW2 #HW12
    elim (IH1 … HWV … HL12 W) -HWV // -HW #V0 #HWV0 #_
    elim (IH1 … HTU2 (L2.ⓛW) … HT20 HT2) -IH1 -HTU2 -HT20 -HT2 // [2: /2 width=1/ ] #U20 #HTU20 #HU20
    lapply (lfpr_inv_fpr L1 L2 … W) [ /2 width=1/ ] -HL12 #HL12
    elim (lsubse_ssta_trans … HTU20 (L2.ⓓV2) ?) -HTU20
    [ #U #HTU20 #HU20 -HWV0 -HL12 -W1 -W2
      @(ex2_intro … (ⓓ{b}V2.U)) [ /2 width=1/ ] -h -l -l1 -V -V0 -T2 -T20 -U0
      @(fpcs_fprs_strap2 ? L1 … (ⓓ{b}V2.U2)) [ /4 width=1/ ] -V1
      /4 width=4 by fpcs_fwd_shift, fpcs_canc_dx, cpcs_fpcs, fpcs_fwd_abst13/
    | -b -l -V -V1 -T2 -T20 -U0 -U2 -U20
      /6 width=6 by lsubse_abbr, fpcs_inv_cpcs, fpcs_canc_sn, fpcs_fprs_strap1, cpcs_fpcs, bi_inj/
    ]
  ]
|   
(*  

fact ssta_ltpr_tpr_aux: ∀h,g,L,T. (
                           ∀L1,T1,U1,l. ⦃h, L1⦄ ⊢ T1 •[g, l] U1 →
                           ∀L2. L1 ⊢ ⬌* L2 → ∀T2. T1 ➡ T2 → ⦃h, L1⦄ ⊩ T1 :[g] →
                           #{L1, T1} < #{L ,T} →
                           ∃∃U2. ⦃h, L2⦄ ⊢ T2 •[g, l] U2 & U1 ➡ U2
                        ) →
                        ∀L1,T1,U1,l. ⦃h, L1⦄ ⊢ T1 •[g, l] U1 →
                        ∀L2. L1 ➡ L2 → ∀T2. T1 ➡ T2 → ⦃h, L1⦄ ⊩ T1 :[g] →
                        L = L1 → T = T1 →
                        ∃∃U2. ⦃h, L2⦄ ⊢ T2 •[g, l] U2 & U1 ➡ U2.
#h #g #L #T #IH #L1 #T1 #U1 #l * -L1 -T1 -U1 -l
[ #L1 #k #l #Hkl #L2 #_ #X #H #_ #H1 #H2 destruct -IH
  >(tpr_inv_atom1 … H) -X /3 width=3/
| #L1 #K1 #V1 #W1 #U1 #i #l #HLK1 #HVW1 #HWU1 #L2 #HL12 #X #H1 #H2 #H3 #H4 destruct
  >(tpr_inv_atom1 … H1) -X
  elim (snv_inv_lref … H2) -H2 #I0 #K0 #V0 #H #HV1
  lapply (ldrop_mono … H … HLK1) -H #H destruct
  lapply (ldrop_pair2_fwd_fw … HLK1 (#i)) #HKV1
  elim (ltpr_ldrop_conf … HLK1 … HL12) -HLK1 -HL12 #X #H #HLK2
  elim (ltpr_inv_pair1 … H) -H #K2 #V2 #HK12 #HV12 #H destruct
  elim (IH … HVW1 K2 … HV12 ? ?) -IH -HVW1 -HV12 // -L1 -V1 /2 width=1/ -K1 #W2 #HVW2 #HW12
  elim (lift_total W2 0 (i+1)) #U2 #HWU2
  lapply (tpr_lift … HW12 … HWU1 … HWU2) -W1 /3 width=6/
| #L1 #K1 #V1 #W1 #U1 #i #l #HLK1 #HVW1 #HVU1 #L2 #HL12 #X #H1 #H2 #H3 #H4 destruct
  >(tpr_inv_atom1 … H1) -X
  elim (snv_inv_lref … H2) -H2 #I0 #K0 #V0 #H #HV1
  lapply (ldrop_mono … H … HLK1) -H #H destruct
  lapply (ldrop_pair2_fwd_fw … HLK1 (#i)) #HKV1
  elim (ltpr_ldrop_conf … HLK1 … HL12) -HLK1 -HL12 #X #H #HLK2
  elim (ltpr_inv_pair1 … H) -H #K2 #V2 #HK12 #HV12 #H destruct
  elim (IH … HVW1 K2 … HV12 ? ?) -IH -HVW1 // -L1 -HV1 /2 width=1/ -K1 #W2 #HVW2 #_ -W1
  elim (lift_total V2 0 (i+1)) #U2 #HVU2
  lapply (tpr_lift … HV12 … HVU1 … HVU2) -V1 /3 width=6/
| #a #I #L1 #V1 #T1 #U1 #l #HTU1 #L2 #HL12 #X #H1 #H2 #H3 #H4 destruct
  elim (snv_inv_bind … H2) -H2 #_ #HT1
  elim (tpr_inv_bind1 … H1) -H1 *
  [ #V2 #T0 #T2 #HV12 #HT10 #HT02 #H destruct
    elim (IH … HTU1 (L2.ⓑ{I}V2) … HT10 ? ?) -IH -HTU1 -HT10 // -T1 /3 width=1/ -L1 #U0 #HTU0 #HU10
    lapply (tps_lsubs_trans … HT02 (L2.ⓑ{I}V2) ?) -HT02 [ /2 width=1/ ] #HT02
    elim (ssta_tps_conf … HTU0 … HT02) -T0 #U2 #HTU2 #HU02
    lapply (tpss_inv_SO2 … HU02) -HU02 #HU02
    lapply (tps_lsubs_trans … HU02 (⋆.ⓑ{I}V2) ?) -HU02
    [ /2 width=1/ | /3 width=7/ ]
  | #T2 #HT12 #HT2 #H1 #H2 destruct
    elim (IH ? ? ? ? HTU1 (L2.ⓓV1) … HT12 ? ?) -IH -HTU1 -HT12 // -T1 [2: /3 width=1/ ] -L1 #U2 #HTU2 #HU12
    elim (ssta_inv_lift1 … HTU2 … HT2) -T2 /3 width=5/
  ]
| #L1 #V1 #T1 #U1 #l #HTU1 #L2 #HL12 #X #H1 #H2 #H3 #H4 destruct
  elim (snv_inv_appl … H2) -H2 #a #W1 #W10 #U10 #l0 #HV1 #HT1 #HVW1 #HW10 #HTU10
  elim (tpr_inv_appl1 … H1) -H1 *
  [ #V2 #T2 #HV12 #HT12 #H destruct -HV1 -HVW1 -HW10 -HTU10
    elim (IH … HTU1 L2 … HT12 HT1 ?) -IH -HTU1 -HT12 -HT1 // [2: /2 width=1/ ] -HL12 /3 width=5/
  | #b #V2 #W #T2 #T20 #HV12 #HT20 #H1 #H2 destruct
    elim (snv_inv_bind … HT1) -HT1 #HW #HT2
    elim (xprs_fwd_abst1 … HTU10) -HTU10 #W11 #U11 #HW11 #H destruct
    elim (ssta_inv_bind1 … HTU1) -HTU1 #U2 #HTU2 #H destruct
    elim (IH … HVW1 L2 … HV12 HV1 ?) -HVW1 -HV1 // [2: /2 width=1/ ] #W2 #HVW2 #HW12 
    lapply (cprs_div … HW11 … HW10) -W11 #HW1
    lapply (cpcs_cpr_strap1 … HW1 W2 ?) [ /2 width=1/ ] -W1 #HW2
    elim (IH … HTU2 (L2.ⓛW2) … HT20 HT2 ?) -IH -HT2 -HT20 //
    [ /5 width=7/ | /3 width=1/ ]
  | #b #V2 #V0 #W0 #W2 #T0 #T2 #HV12 #W02 #HT02 #HV20 #H1 #H2 destruct
    elim (snv_inv_bind … HT1) -HT1 #HW0 #HT0
    elim (ssta_inv_bind1 … HTU1) -HTU1 #U0 #HTU0 #H destruct
    
    
    elim (xprs_fwd_abst1 … HTU10) -HTU10 #W11 #U11 #HW11 #H destruct
  
fact snv_ltpr_tpr_aux: ∀h,g,L,T. (
                          ∀L1,T1,U1,l. ⦃h, L1⦄ ⊢ T1 •[g, l] U1 →
                          ∀L2. L1 ➡ L2 → ∀T2. T1 ➡ T2 → ⦃h, L1⦄ ⊩ T1 :[g] →
                          h ⊢ ⦃L, T⦄ •⭃*[g] ⦃L1 ,T1⦄ →
                          ∃∃U2. ⦃h, L2⦄ ⊢ T2 •[g, l] U2 & ⦃L1, U1⦄ ⬌* ⦃L2, U2⦄
                       ) → (
                          ∀L1,T1. ⦃h, L1⦄ ⊩ T1 :[g] →
                          ∀L2. L1 ➡ L2 → ∀T2. ⦃h, L2⦄ ⊢ T1 •➡*[g] T2 →
                          h ⊢ ⦃L, T⦄ •⭃*[g] ⦃L1 ,T1⦄ → ⦃h, L2⦄ ⊩ T2 :[g]
                       ) →
                       ∀L1,T1. ⦃h, L1⦄ ⊩ T1 :[g] →
                       ∀L2. L1 ➡ L2 → ∀T2. T1 ➡ T2 →
                       L = L1 → T = T1 → ⦃h, L2⦄ ⊩ T2 :[g].
#h #g #L #T #IH2 #IH1 #L1 #T1 * -L1 -T1
[ #L1 #k #L2 #_ #X #H #H1 #H2 destruct -IH2 -IH1 -L1
  >(tpr_inv_atom1 … H) -X //
| #I #L1 #K1 #V1 #i #HLK1 #HV1 #L2 #HL12 #X #H #H1 #H2 destruct -IH2
  >(tpr_inv_atom1 … H) -X
  elim (ltpr_ldrop_conf … HLK1 … HL12) -HL12 #X #H #HLK2
  elim (ltpr_inv_pair1 … H) -H #K2 #V2 #HK12 #HV12 #H destruct
  lapply (IH1 … HV1 … HK12 V2 ? ?) -IH1 -HV1 -HK12 /4 width=1/ -HV12 /3 width=4/ -HLK1 /3 width=5/
| #a #I #L1 #V1 #T1 #HV1 #HT1 #L2 #HL12 #X #H #H1 #H2 destruct -IH2
  elim (tpr_inv_bind1 … H) -H *
  [ #V2 #T0 #T2 #HV12 #HT10 #HT02 #H destruct
    lapply (tps_lsubs_trans … HT02 (L2.ⓑ{I}V2) ?) -HT02 /2 width=1/ #HT02
    lapply (cpr_intro (L2.ⓑ{I}V2) … T2 0 1 HT10 ?) -HT10 /2 width=1/ -HT02 #HT12
    lapply (IH1 … HV1 … HL12 V2 ? ?) -HV1 /4 width=1/ #HV2
    lapply (IH1 … HT1 (L2.ⓑ{I}V2) … T2 ? ?) -IH1 -HT1 /3 width=1/
  | #T2 #HT12 #HXT2 #H1 #H2 destruct
    lapply (IH1 … HT1 (L2.ⓓV1) ? T2 ? ?) -IH1 -HT1 /4 width=1/ -HT12 -HL12 #HT2
    lapply (snv_inv_lift … HT2 L2 … HXT2) -T2 // /2 width=1/
  ]
| #a #L1 #V1 #W1 #W10 #T1 #U1 #l #HV1 #HT1 #HVW1 #HW10 #HTU1 #L2 #HL12 #X #H #H1 #H2 destruct
  elim (tpr_inv_appl1 … H) -H *
  [ #V2 #T2 #HV12 #HT12 #H destruct
    lapply (IH1 … HV1 … HL12 V2 ? ?) /4 width=1/ #HV2
    lapply (IH1 … HT1 … HL12 T2 ? ?) /4 width=1/ #HT2
    lapply (IH1 … HT1 … HTU1 ?) -IH1 -HT1 // /2 width=1/ #H
    elim (snv_inv_bind … H) -H #HW10 #HU1
    elim (IH2 … HVW1 … HL12 … HV12 HV1 ?) -IH2 -HVW1 -HL12 -HV12 -HV1 /2 width=1/ #W2 #HVW2 #HW12
    lapply (fpcs_canc_sn L1 L1 … W10 … HW12) -HW12 /3 width=1/ -W1 #HW102
    @(snv_appl … HV2 HT2 HVW2)
*)
