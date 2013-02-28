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

include "basic_2/dynamic/snv_ltpr_ssta.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

(* Properties on context-free parallel reduction for local environments *****)

fact snv_ltpr_tpr_aux: ∀h,g,L0,T0.
                       (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_ssta_ltpr_tpr h g L1 T1) →
                       (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_snv_ltpr_tpr h g L1 T1) →
                       ∀L1,T1. L0 = L1 → T0 = T1 → IH_snv_ltpr_tpr h g L1 T1.
#h #g #L0 #T0 #IH2 #IH1 #L1 * * [||||*]
[ #k #HL0 #HT0 #H1 #L2 #_ #X #H2 destruct -IH2 -IH1 -L1
  >(tpr_inv_atom1 … H2) -X //
| #i #HL0 #HT0 #H1 #L2 #HL12 #X #H2 destruct -IH2
  elim (snv_inv_lref … H1) -H1 #I #K1 #V1 #HLK1 #HV1
  >(tpr_inv_atom1 … H2) -X
  elim (ltpr_ldrop_conf … HLK1 … HL12) -HL12 #X #H #HLK2
  elim (ltpr_inv_pair1 … H) -H #K2 #V2 #HK12 #HV12 #H destruct
  lapply (ldrop_pair2_fwd_fw … HLK1 (#i)) -HLK1 #HLK1
  lapply (IH1 … HK12 … HV12) -IH1 -HV12 -HK12 // -HV1 [ /2 width=1/ ] -HLK1 /2 width=5/
| #p #HL0 #HT0 #H1 #L2 #HL12 #X #H2 destruct -IH2 -IH1
  elim (snv_inv_gref … H1)
| #a #I #V1 #T1 #HL0 #HT0 #H1 #L2 #HL12 #X #H2 destruct -IH2
  elim (snv_inv_bind … H1) -H1 #HV1 #HT1
  elim (tpr_inv_bind1 … H2) -H2 *
  [ #V2 #T0 #T2 #HV12 #HT10 #HT02 #H destruct
    lapply (tps_lsubs_trans … HT02 (L2.ⓑ{I}V2) ?) -HT02 /2 width=1/ #HT02
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
  [ #V2 #T2 #HV12 #HT12 #H destruct
    lapply (IH1 … HV1 … HL12 … HV12) [ /2 width=1/ ] #HV2
    lapply (IH1 … HT1 … HL12 … HT12) [ /2 width=1/ ] #HT2
    elim (IH2 … HVW1 … HL12 … HV12) -IH2 -HVW1 -HV12 // -HV1 [2: /2 width=1/ ] #W2 #HVW2 #HW12
    lapply (fpcs_canc_sn L1 L1 … W10 W1 … HW12) -HW12 /3 width=1/ -W10 #HW12
    @(snv_appl … HV2 HT2 HVW2)
(*
    lapply (IH1 … HT1 … HTU1) -IH1 // #H
    elim (snv_inv_bind … H) -H #HW1 #HU1
    elim (IH2 … HVW1 … HL12 … HV12 HV1) -IH2 -HVW1 -HV12 -HV1 // #W2 #HVW2 #HW12
*)
