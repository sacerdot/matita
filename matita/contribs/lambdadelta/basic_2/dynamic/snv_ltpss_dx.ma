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

include "basic_2/computation/dxprs_ltpss_dx.ma".
include "basic_2/equivalence/cpcs_ltpss_dx.ma".
include "basic_2/dynamic/snv_lift.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

(* Properties about dx parallel unfold **************************************)

lemma snv_ltpss_dx_tpss_conf: ∀h,g,L1,T1. ⦃h, L1⦄ ⊢ T1 ¡[g] →
                              ∀L2,d,e. L1 ▶* [d, e] L2 →
                              ∀T2. L2 ⊢ T1 ▶* [d, e] T2 → ⦃h, L2⦄ ⊢ T2 ¡[g].
#h #g #L1 #T1 #H elim H -L1 -T1
[ #L1 #k #L2 #d #e #_ #X #H
   >(tpss_inv_sort1 … H) -X //
| #I #L1 #K1 #V1 #i #HLK1 #HV1 #IHV1 #L2 #d #e #HL12 #X #H
  elim (tpss_inv_lref1 … H) -H
  [ #H destruct
    elim (lt_or_ge i d) #Hdi [ | elim (lt_or_ge i (d + e)) #Hide ]
    [ elim (ltpss_dx_ldrop_conf_le … HL12 … HLK1 …) -L1 /2 width=2/ #X #H #HLK2
      elim (ltpss_dx_inv_tpss11 … H …) -H /2 width=1/ #K2 #V2 #HK12 #HV12 #H destruct
      lapply (IHV1 … HK12 … HV12) -IHV1 -HK12 -HV12 /2 width=5/
    | elim (ltpss_dx_ldrop_conf_be … HL12 … HLK1 …) -L1 // /2 width=2/ #X #H #HLK2
      elim (ltpss_dx_inv_tpss21 … H …) -H /2 width=1/ #K2 #V2 #HK12 #HV12 #H destruct
      lapply (IHV1 … HK12 … HV12) -IHV1 -HK12 -HV12 /2 width=5/
    | lapply (ltpss_dx_ldrop_conf_ge … HL12 … HLK1 ?) -L1 // -Hide /2 width=5/
    ]
  | * #K2 #V2 #W2 #Hdi #Hide #HLK2 #HVW2 #HWT2
    elim (ltpss_dx_ldrop_conf_be … HL12 … HLK1 …) -L1 // /2 width=2/ #X #H1 #H2
    elim (ltpss_dx_inv_tpss21 … H1 …) -H1 /2 width=1/ #K0 #V0 #HK12 #HV12 #H destruct
    lapply (ldrop_mono … H2 … HLK2) -H2 #H destruct
    lapply (ldrop_fwd_ldrop2 … HLK2) -HLK2 #HLK2
    lapply (tpss_trans_eq … HV12 HVW2) -V2 #HV1W2
    lapply (IHV1 … HK12 … HV1W2) -IHV1 -HK12 -HV1W2 /2 width=7/
  ]
| #a #I #L1 #V1 #T1 #_ #_ #IHV1 #IHT1 #L2 #d #e #HL12 #X #H
  elim (tpss_inv_bind1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct
  lapply (IHV1 … HL12 … HV12) -IHV1 #HV2
  lapply (IHT1 … HT12) -IHT1 -HT12 /2 width=1/
| #a #L1 #V1 #W1 #W0 #T1 #U1 #l #_ #_ #HVW1 #HW10 #HTU1 #IHV1 #IHT1 #L2 #d #e #HL12 #X #H
  elim (tpss_inv_flat1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct
  lapply (IHV1 … HL12 … HV12) -IHV1 #HV2
  lapply (IHT1 … HT12) -IHT1 /2 width=1/ #HT2
  elim (ssta_ltpss_dx_tpss_conf … HVW1 … HL12 … HV12) -V1 #W2 #HVW2 #HW12
  elim (dxprs_ltpss_dx_tpss_conf … HTU1 … HL12 … HT12) -T1 #X #HTU2 #H
  elim (tpss_inv_bind1 … H) -H #W #U2 #HW0 #_ #H -U1 destruct
  elim (cprs_ltpss_dx_tpss2_conf … HW10 … HL12 … HW12 … HW0) -L1 -W1 -W0 #W0 #HW20 #HW0
  lapply (dxprs_strap1 … (ⓛ{a}W0.U2) HTU2 ?) -HTU2 /3 width=3/ -HW0 /2 width=8/
| #L1 #W1 #T1 #U1 #l #_ #_ #HTU1 #HUW1 #IHW1 #IHT1 #L2 #d #e #HL12 #X #H
  elim (tpss_inv_flat1 … H) -H #W2 #T2 #HW12 #HT12 #H destruct
  lapply (IHW1 … HL12 … HW12) -IHW1 #HW2
  lapply (IHT1 … HL12 … HT12) -IHT1 #HT2
  elim (ssta_ltpss_dx_tpss_conf … HTU1 … HL12 … HT12) -T1 #U2 #HTU2 #HU12
  lapply (cpcs_ltpss_dx_tpss2_conf … HL12 … HUW1 … HU12 … HW12) -L1 -W1 -U1 /2 width=4/
]
qed-.

lemma snv_ltpss_dx_conf: ∀h,g,L1,T. ⦃h, L1⦄ ⊢ T ¡[g] →
                         ∀L2,d,e. L1 ▶* [d, e] L2 → ⦃h, L2⦄ ⊢ T ¡[g].
#h #g #L1 #T #HT #L2 #d #e #HL12
@(snv_ltpss_dx_tpss_conf … HT … HL12) //
qed-.

lemma snv_tpss_conf: ∀h,g,L,T1. ⦃h, L⦄ ⊢ T1 ¡[g] →
                     ∀T2,d,e. L ⊢ T1 ▶* [d, e] T2 → ⦃h, L⦄ ⊢ T2 ¡[g].
#h #g #L #T1 #HT1 #T2 #d #e #HT12
@(snv_ltpss_dx_tpss_conf … HT1 … HT12) //
qed-.

lemma snv_tps_conf: ∀h,g,L,T1. ⦃h, L⦄ ⊢ T1 ¡[g] →
                    ∀T2,d,e. L ⊢ T1 ▶ [d, e] T2 → ⦃h, L⦄ ⊢ T2 ¡[g].
#h #g #L #T1 #HT1 #T2 #d #e #HT12
@(snv_tpss_conf … HT1 T2) /2 width=3/
qed-.
