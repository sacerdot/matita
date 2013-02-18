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
include "basic_2/dynamic/snv_fpr_ssta.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

(* Properties on context-free parallel reduction for closures ***************)

fact snv_ltpr_tpr_aux: ∀h,g,n. (
                          ∀L1,T1. ♯{L1, T1} < n →
                          ∀U1,l. ⦃h, L1⦄ ⊢ T1 •[g, l] U1 →
                          ∀L2. L1 ➡ L2 → ∀T2. T1 ➡ T2 → ⦃h, L1⦄ ⊩ T1 :[g] →
                          ∃∃U2. ⦃h, L2⦄ ⊢ T2 •[g, l] U2 & ⦃L1, U1⦄ ⬌* ⦃L2, U2⦄
                       ) → (
                          ∀L1,T1. ♯{L1, T1} < n → ⦃h, L1⦄ ⊩ T1 :[g] →
                          ∀L2. L1 ➡ L2 → ∀T2. ⦃h, L2⦄ ⊢ T1 •*➡*[g] T2 → ⦃h, L2⦄ ⊩ T2 :[g]
                       ) →
                       ∀L1,T1. ♯{L1, T1} = n → ⦃h, L1⦄ ⊩ T1 :[g] →
                       ∀L2. L1 ➡ L2 → ∀T2. T1 ➡ T2 → ⦃h, L2⦄ ⊩ T2 :[g].
#h #g #n #IH2 #IH1 #L1 * * [||||*]
[ #k #Hn #H1 #L2 #_ #X #H2 destruct -IH2 -IH1 -L1
  >(tpr_inv_atom1 … H2) -X //
| #i #Hn #H1 #L2 #HL12 #X #H2 destruct -IH2
  elim (snv_inv_lref … H1) -H1 #I #K1 #V1 #HLK1 #HV1
  >(tpr_inv_atom1 … H2) -X
  elim (ltpr_ldrop_conf … HLK1 … HL12) -HL12 #X #H #HLK2
  elim (ltpr_inv_pair1 … H) -H #K2 #V2 #HK12 #HV12 #H destruct
  lapply (ldrop_pair2_fwd_fw … HLK1 (#i)) -HLK1 #HLK1
  lapply (IH1 … HV1 … HK12 V2 ?) -IH1 -HV1 -HK12 //
  [ @cprs_dxprs /3 width=1/ (**) (* auto: /4 width=1/ fails *)
  ] -HV12 /2 width=5/
| #p #Hn #H1 #L2 #HL12 #X #H2 destruct -IH2
  elim (snv_inv_gref … H1)
| #a #I #V1 #T1 #Hn #H1 #L2 #HL12 #X #H2 destruct -IH2
  elim (snv_inv_bind … H1) -H1 #HV1 #HT1
  elim (tpr_inv_bind1 … H2) -H2 *
  [ #V2 #T0 #T2 #HV12 #HT10 #HT02 #H destruct
    lapply (tps_lsubs_trans … HT02 (L2.ⓑ{I}V2) ?) -HT02 /2 width=1/ #HT02
    lapply (cpr_intro (L2.ⓑ{I}V2) … T2 0 1 HT10 ?) -HT10 /2 width=1/ -HT02 #HT12
    lapply (IH1 … HV1 … HL12 V2 ?) -HV1 //
    [ @cprs_dxprs /3 width=1/ (**) (* auto: /4 width=1/ fails *)
    ] #HV2
    lapply (IH1 … HT1 (L2.ⓑ{I}V2) … T2 ?) -IH1 -HT1 /3 width=1/
  | #T2 #HT12 #HXT2 #H1 #H2 destruct
    lapply (IH1 … HT1 (L2.ⓓV1) … T2 ?) -IH1 -HT1 // /2 width=2/
    [ @cprs_dxprs /3 width=1/ (**) (* auto: /4 width=1/ fails *)
    ] -HT12 -HL12 #HT2
    lapply (snv_inv_lift … HT2 L2 … HXT2) -T2 // /2 width=1/
  ]
| #V1 #T1 #Hn #H1 #L2 #HL12 #X #H2 destruct
  elim (snv_inv_appl … H1) -H1 #a #W10 #W1 #U1 #l #HV1 #HT1 #HVW1 #HW10 #HTU1
  elim (tpr_inv_appl1 … H2) -H2 *
  [ #V2 #T2 #HV12 #HT12 #H destruct
    lapply (IH1 … HV1 … HL12 V2 ?) 
    [ @cprs_dxprs /3 width=1/ (**) (* auto: /4 width=1/ fails *)
    | //
    ] #HV2
    lapply (IH1 … HT1 … HL12 T2 ?)
    [ @cprs_dxprs /3 width=1/ (**) (* auto: /4 width=1/ fails *)
    | //
    ] #HT2
    lapply (IH1 … HT1 … HTU1) -IH1 // #H
    elim (snv_inv_bind … H) -H #HW1 #HU1
    elim (IH2 … HVW1 … HL12 … HV12 HV1) -IH2 -HVW1 -HV12 -HV1 // #W2 #HVW2 #HW12
    lapply (fpcs_canc_sn L1 L1 … W10 W1 … HW12) -HW12 /3 width=1/ -W10 #HW12
    @(snv_appl … HV2 HT2 HVW2)
