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

include "basic_2/computation/dxprs_lpss.ma".
include "basic_2/equivalence/cpcs_lpss.ma".
include "basic_2/dynamic/snv_lift.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

(* Properties about sn parallel substitution for local environments *********)

lemma snv_cpss_lpss_conf: ∀h,g,L1,T1. ⦃h, L1⦄ ⊢ T1 ¡[g] → ∀T2. L1 ⊢ T1 ▶* T2 →
                          ∀L2. L1 ⊢ ▶* L2 → ⦃h, L2⦄ ⊢ T2 ¡[g].
#h #g #L1 #T1 #H elim H -L1 -T1
[ #L1 #k #X #H #L2 #_
   >(cpss_inv_sort1 … H) -X //
| #I #L1 #K1 #V1 #i #HLK1 #_ #IHV1 #W2 #H #L2 #HL12
  elim (cpss_inv_lref1 … H) -H
  [ #H destruct
    elim (lpss_ldrop_conf … HLK1 … HL12) -L1 #X #H #HLK2
    elim (lpss_inv_pair1 … H) -H #K2 #V2 #HK12 #HV12 #H destruct
    lapply (IHV1 … HV12 … HK12) -IHV1 -HV12 -HK12 /2 width=5/
  | * #K0 #V0 #V2 #HLK0 #HV12 #HVW2
    lapply (ldrop_mono … HLK0 … HLK1) -HLK0 #H destruct
    elim (lpss_ldrop_conf … HLK1 … HL12) -L1 #X #H #HLK2
    elim (lpss_inv_pair1 … H) -H #K2 #V #HK12 #_ #H destruct
    lapply (ldrop_fwd_ldrop2 … HLK2) -V #HLK2
    lapply (IHV1 … HV12 … HK12) -IHV1 -HV12 -HK12 /2 width=7/
  ]
| #a #I #L1 #V1 #T1 #_ #_ #IHV1 #IHT1 #X #H #L2 #HL12
  elim (cpss_inv_bind1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct
  lapply (IHV1 … HV12 … HL12) -IHV1 #HV2
  lapply (IHT1 … HT12 (L2.ⓑ{I}V2) ?) -IHT1 -HT12 /2 width=1/
| #a #L1 #V1 #W1 #W0 #T1 #U1 #l #_ #_ #HVW1 #HW10 #HTU1 #IHV1 #IHT1 #X #H #L2 #HL12
  elim (cpss_inv_flat1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct
  lapply (IHV1 … HV12 … HL12) -IHV1 #HV2
  lapply (IHT1 … HT12 … HL12) -IHT1 #HT2
  elim (ssta_cpss_lpss_conf … HVW1 … HV12 … HL12) -V1 #W2 #HVW2 #HW12
  elim (dxprs_cpss_lpss_conf … HTU1 … HT12 … HL12) -T1 #X #HTU2 #H
  elim (cpss_inv_bind1 … H) -H #W #U2 #HW0 #_ #H -U1 destruct
  elim (cprs_cpss2_lpss_conf_dx … HW10 … HW12 … HW0 … HL12) -L1 -W1 -W0 #W0 #HW20 #HW0
  lapply (dxprs_strap1 … (ⓛ{a}W0.U2) HTU2 ?) -HTU2 /3 width=3/ -HW0 /2 width=8/
| #L1 #W1 #T1 #U1 #l #_ #_ #HTU1 #HUW1 #IHW1 #IHT1 #X #H #L2 #HL12
  elim (cpss_inv_flat1 … H) -H #W2 #T2 #HW12 #HT12 #H destruct
  lapply (IHW1 … HW12 … HL12) -IHW1 #HW2
  lapply (IHT1 … HT12 … HL12) -IHT1 #HT2
  elim (ssta_cpss_lpss_conf … HTU1 … HT12 … HL12) -T1 #U2 #HTU2 #HU12
  lapply (cpcs_cpss2_lpss_conf … HUW1 … HU12 … HW12 … HL12) -L1 -W1 -U1 /2 width=4/
]
qed-.

lemma snv_lpss_conf: ∀h,g,L1,T. ⦃h, L1⦄ ⊢ T ¡[g] →
                     ∀L2. L1 ⊢ ▶* L2 → ⦃h, L2⦄ ⊢ T ¡[g].
#h #g #L1 #T #HT #L2 #HL12
@(snv_cpss_lpss_conf … HT … HL12) //
qed-.

lemma snv_cpss_conf: ∀h,g,L,T1. ⦃h, L⦄ ⊢ T1 ¡[g] →
                     ∀T2. L ⊢ T1 ▶* T2 → ⦃h, L⦄ ⊢ T2 ¡[g].
#h #g #L #T1 #HT1 #T2 #HT12
@(snv_cpss_lpss_conf … HT1 … HT12) //
qed-.
