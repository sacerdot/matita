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

include "basic_2/static/ssta_ltpss_sn.ma".
include "basic_2/computation/dxprs_lift.ma".
include "basic_2/equivalence/lsubse_ssta.ma".
include "basic_2/equivalence/fpcs_cpcs.ma".
include "basic_2/equivalence/lfpcs_fpcs.ma".
include "basic_2/dynamic/snv_ssta.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

(* Properties on context-free parallel reduction for closures ***************)

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
[ #k #_ #Y #l #H1 #L2 #HL12 #X #H2 #_ -IH3 -IH2 -IH1
  elim (ssta_inv_sort1 … H1) -H1 #Hkl #H destruct
  >(tpr_inv_atom1 … H2) -X /4 width=6/
| #i #Hn #U1 #l #H1 #L2 #HL12 #X #H2 #H3 destruct -IH3 -IH2
  elim (ssta_inv_lref1 … H1) -H1 * #K1
  >(tpr_inv_atom1 … H2) -X
  elim (snv_inv_lref … H3) -H3 #I0 #K0 #V0 #H #HV1
  [ #V1 #W1 #HLK1 #HVW1 #HWU1
    lapply (ldrop_mono … H … HLK1) -H #H destruct
    lapply (ldrop_pair2_fwd_fw … HLK1 (#i)) #HKV1
    elim (ltpr_ldrop_conf … HLK1 … HL12) #X #H #HLK2
    elim (ltpr_inv_pair1 … H) -H #K2 #V2 #HK12 #HV12 #H destruct
    elim (IH1 … HVW1 K2 … HV12) -IH1 -HVW1 -HV12 // -HV1 -HKV1 #W2 #HVW2 #HW12
    lapply (ldrop_fwd_ldrop2 … HLK1) -V1 #H1
    lapply (ldrop_fwd_ldrop2 … HLK2) #H2
    elim (lift_total W2 0 (i+1)) #U2 #HWU2
    lapply (fpcs_lift … HW12 … H1 H2 … HWU1 … HWU2) -H1 -H2 -W1 [ /3 width=1/ ] /3 width=6/
  | #V1 #W1 #l0 #HLK1 #HVW1 #HVU1 #H destruct
    lapply (ldrop_mono … H … HLK1) -H #H destruct
    lapply (ldrop_pair2_fwd_fw … HLK1 (#i)) #HKV1
    elim (ltpr_ldrop_conf … HLK1 … HL12) -HLK1 #X #H #HLK2
    elim (ltpr_inv_pair1 … H) -H #K2 #V2 #HK12 #HV12 #H destruct
    elim (IH1 … HVW1 K2 … HV12) -IH1 -HVW1 // -HV1 -HK12 -HKV1 #W2 #HVW2 #_ -W1
    elim (lift_total V2 0 (i+1)) #U2 #HVU2
    lapply (tpr_lift … HV12 … HVU1 … HVU2) -V1 /4 width=6/
  ]
| #p #Hn #U1 #l #H1 -IH3 -IH1
  elim (ssta_inv_gref1 … H1)
| #a #I #V1 #T1 #Hn #Y #l #H1 #L2 #HL12 #X #H2 #H3 destruct -IH3 -IH2
  elim (ssta_inv_bind1 … H1) -H1 #U1 #HTU1 #H destruct
  elim (snv_inv_bind … H3) -H3 #_ #HT1
  elim (tpr_inv_bind1 … H2) -H2 *
  [ #V2 #T0 #T2 #HV12 #HT10 #HT02 #H destruct
    elim (IH1 … HTU1 (L2.ⓑ{I}V2) … HT10) -IH1 -HTU1 -HT10 // -T1 /3 width=1/ -HL12 #U0 #HTU0 #HU10
    lapply (tps_lsubs_trans … HT02 (L2.ⓑ{I}V2) ?) -HT02 [ /2 width=1/ ] #HT02
    elim (ssta_tps_conf … HTU0 … HT02) -T0 #U2 #HTU2 #HU02
    lapply (cpr_intro … U0 … HU02) -HU02 // #HU02
    lapply (fpcs_fpr_strap1 … HU10 (L2.ⓑ{I}V2) U2 ?) [ /2 width=1/ ] -U0 #HU12
    lapply (fpcs_fwd_shift … HU12 a) -HU12 /3 width=3/
  | #T2 #HT12 #HT2 #H1 #H2 destruct
    elim (IH1 … HTU1 (L2.ⓓV1) … HT12) -IH1 -HTU1 -HT12 // -T1 [2: /3 width=1/ ] -HL12 #U2 #HTU2 #HU12
    lapply (fpcs_fwd_shift … HU12 true) -HU12 #HU12
    elim (ssta_inv_lift1 … HTU2 … HT2) -T2 [3: /2 width=1/ |2: skip ] #U #HXU #HU2
    lapply (fpcs_fpr_strap1 … HU12 L2 U ?) -HU12 [ /3 width=3/ ] -U2 /2 width=3/
  ]
| #V1 #T1 #Hn #Y #l #H1 #L2 #HL12 #X #H2 #H3 destruct
  elim (ssta_inv_appl1 … H1) -H1 #U1 #HTU1 #H destruct
  elim (snv_inv_appl … H3) -H3 #a #W1 #W10 #U10 #l0 #HV1 #HT1 #HVW1 #HW10 #HTU10
  elim (tpr_inv_appl1 … H2) -H2 *
  [ #V2 #T2 #HV12 #HT12 #H destruct -a -l0 -W1 -W10 -U10 -HV1 -IH3 -IH2
    elim (IH1 … HTU1 … HL12 … HT12 HT1) -IH1 -HTU1 -HL12 -HT12 -HT1 // /3 width=5/
  | #b #V2 #W #T2 #T20 #HV12 #HT20 #H1 #H2 destruct
    elim (snv_inv_bind … HT1) -HT1 #HW #HT2
    elim (ssta_inv_bind1 … HTU1) -HTU1 #U2 #HTU2 #H destruct
    elim (dxprs_inv_abst1 … HTU10) -HTU10 #W0 #U0 #HW0 #_ #H destruct
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
  | #b #V0 #V2 #W0 #W2 #T0 #T2 #HV10 #HW02 #HT02 #HV02 #H1 #H2 destruct -a -l0 -W1 -W10 -HV1 -IH3 -IH2
    elim (ssta_inv_bind1 … HTU1) -HTU1 #U0 #HTU0 #H destruct
    elim (snv_inv_bind … HT1) -HT1 #_ #HT0
    elim (IH1 … HTU0 (L2.ⓓW2) … HT02 HT0) -IH1 -HTU0 -HT02 -HT0 // -T0 [2: /2 width=1/ ] -HL12 -HW02 #U2 #HTU2 #HU02
    lapply (fpcs_fwd_shift … HU02 b) -HU02 #HU02
    lapply (fpcs_flat_dx_tpr … HU02 … HV10 Appl) -HV10 -HU02 #HU02
    lapply (fpcs_fpr_strap1 … HU02 L2 (ⓓ{b}W2.ⓐV2.U2) ?) -HU02 [ @ltpr_tpr_fpr // /2 width=3/ ] -V0 /4 width=3/ 
  ]
| #U0 #T1 #Hn #U1 #l #H1 #L2 #HL12 #X #H2 #H3 destruct -IH3 -IH2
  lapply (ssta_inv_cast1 … H1) -H1 #HTU1
  elim (snv_inv_cast … H3) -H3 #T0 #l0 #_ #HT1 #HT10 #_
  elim (ssta_mono … HT10 … HTU1) -HT10 #H1 #H2 destruct
  elim (tpr_inv_cast1 … H2) -H2
  [ * #U2 #T2 #_ #HT12 #H destruct
    elim (IH1 … HTU1 … HL12 … HT12 HT1) -IH1 -HTU1 -HL12 -HT12 -HT1 // -T1 -U0 /3 width=3/
  | #HT1X
    elim (IH1 … HTU1 … HL12 … HT1X HT1) -IH1 -HTU1 -HL12 -HT1X -HT1 // -U0 -T1 /2 width=3/
  ]
]
qed-.

fact ssta_ltpr_cpr_aux: ∀h,g,n. (
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
                           ∀L2. L1 ➡ L2 → ∀T2. L2 ⊢ T1 ➡ T2 → ⦃h, L1⦄ ⊩ T1 :[g] → 
                           ∃∃U2. ⦃h, L2⦄ ⊢ T2 •[g, l] U2 & ⦃L1, U1⦄ ⬌* ⦃L2, U2⦄
                        ) →
                        ∀L1,T1. ♯{L1,T1} = n →
                        ∀U1,l. ⦃h, L1⦄ ⊢ T1 •[g, l] U1 →
                        ∀L2. L1 ➡ L2 → ∀T2. L2 ⊢ T1 ➡ T2 → ⦃h, L1⦄ ⊩ T1 :[g] →
                        ∃∃U2. ⦃h, L2⦄ ⊢ T2 •[g, l] U2 & ⦃L1, U1⦄ ⬌* ⦃L2, U2⦄.
#h #g #n #IH3 #IH2 #IH1 #L1 #T1 #Hn #U1 #l #HTU1 #L2 #HL12 #T2 * #T0 #HT10 #HT02 #HT1
elim (ssta_ltpr_tpr_aux … IH3 IH2 … Hn … HTU1 … HL12 … HT10 HT1)
-T1 -IH3 -IH2 -HL12 [2: /3 width=5/ ] -n #U0 #HTU0 #HU10
elim (ssta_tpss_conf … HTU0 … HT02) -T0 #U2 #HTU2 #HU02
lapply (fpcs_fpr_strap1 … HU10 L2 U2 ?) -HU10 /2 width=3/ -HTU2 /3 width=3/
qed-.

fact ssta_fpr_aux: ∀h,g,n. (
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
                      ∀L2,T2. ⦃L1, T1⦄ ➡ ⦃L2, T2⦄ →  ⦃h, L1⦄ ⊩ T1 :[g] →
                      ∃∃U2. ⦃h, L2⦄ ⊢ T2 •[g, l] U2 & ⦃L1, U1⦄ ⬌* ⦃L2, U2⦄
                   ) →
                   ∀L1,T1. ♯{L1,T1} = n →
                   ∀U1,l. ⦃h, L1⦄ ⊢ T1 •[g, l] U1 →
                   ∀L2,T2. ⦃L1, T1⦄ ➡ ⦃L2, T2⦄ → ⦃h, L1⦄ ⊩ T1 :[g] →
                   ∃∃U2. ⦃h, L2⦄ ⊢ T2 •[g, l] U2 & ⦃L1, U1⦄ ⬌* ⦃L2, U2⦄.
#h #g #n #IH3 #IH2 #IH1 #L1 #T1 #Hn #U1 #l #HTU1 #L2 #T2 #H12 #HT1
elim (fpr_inv_all … H12) -H12 #L #HL1 #HT12 #HL2
elim (ssta_ltpr_cpr_aux … IH3 IH2 … Hn … HTU1 … HL1 … HT12 HT1)
-T1 -IH3 -IH2 -HL1 [2: /3 width=5/ ] -n #U #HTU #HU1
elim (ssta_ltpss_sn_conf … HTU … HL2) -HTU #U2 #HTU2 #HU2
lapply (fpcs_fpr_strap1 … HU1 L2 U2 ?) -HU1 /2 width=3/ -HTU2 /3 width=4/
qed-.
