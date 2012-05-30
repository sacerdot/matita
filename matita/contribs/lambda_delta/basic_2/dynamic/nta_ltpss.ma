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

include "basic_2/equivalence/cpcs_ltpss.ma".
include "basic_2/dynamic/nta_nta.ma".

(* NATIVE TYPE ASSIGNMENT ON TERMS ******************************************)

(* Properties about parallel unfold *****************************************)

lemma nta_ltpss_tpss_conf: ∀h,L1,T1,U. ⦃h, L1⦄ ⊢ T1 : U →
                           ∀L2,d,e. L1 ▶* [d, e] L2 →
                           ∀T2. L2 ⊢ T1 ▶* [d, e] T2 → ⦃h, L2⦄ ⊢ T2 : U.
#h #L1 #T1 #U #H @(nta_ind_alt … H) -L1 -T1 -U
[ #L1 #k #L2 #d #e #_ #T2 #H
  >(tpss_inv_sort1 … H) -H //
| #L1 #K1 #V1 #W #U #i #HLK1 #_ #HWU #IHV1 #L2 #d #e #HL12 #T2 #H
  elim (tpss_inv_lref1 … H) -H
  [ #H destruct
    elim (lt_or_ge i d) #Hdi
    [ elim (ltpss_ldrop_conf_le … HL12 … HLK1 ?) -L1 /2 width=2/ #X #H #HLK2
      elim (ltpss_inv_tpss11 … H ?) -H /2 width=1/ -Hdi #K2 #V2 #HK12 #HV12 #H destruct
      /3 width=7/
    | elim (lt_or_ge i (d + e)) #Hide [ | -Hdi ]
      [ elim (ltpss_ldrop_conf_be … HL12 … HLK1 ? ?) -L1 // /2 width=2/ #X #H #HLK2
        elim (ltpss_inv_tpss21 … H ?) -H /2 width=1/ -Hdi -Hide #K2 #V2 #HK12 #HV12 #H destruct
        /3 width=7/
      | lapply (ltpss_ldrop_conf_ge … HL12 … HLK1 ?) -L1 // -Hide /3 width=7/
      ]
    ]
  | * #K2 #V2 #W2 #Hdi #Hide #HLK2 #HVW2 #HWT2
    elim (ltpss_ldrop_conf_be … HL12 … HLK1 ? ?) -L1 // /2 width=2/ #X #H #HL2K0
    elim (ltpss_inv_tpss21 … H ?) -H /2 width=1/ -Hdi -Hide #K0 #V0 #HK12 #HV12 #H destruct
    lapply (ldrop_mono … HL2K0 … HLK2) -HL2K0 #H destruct
    lapply (ldrop_fwd_ldrop2 … HLK2) -HLK2 #HLK2
    lapply (tpss_trans_eq … HV12 HVW2) -V2 /3 width=9/
  ]
| #L1 #K1 #W1 #V1 #U1 #i #HLK1 #HWV1 #HWU1 #IHWV1 #L2 #d #e #HL12 #T2 #H
  elim (tpss_inv_lref1 … H) -H [ | -HWV1 -HWU1 -IHWV1 ]
  [ #H destruct
    elim (lift_total V1 0 (i+1)) #W #HW
    elim (lt_or_ge i d) #Hdi [ -HWV1 ]
    [ elim (ltpss_ldrop_conf_le … HL12 … HLK1 ?) -L1 /2 width=2/ #X #H #HLK2
      elim (ltpss_inv_tpss11 … H ?) -H /2 width=1/ -Hdi #K2 #W2 #HK12 #HW12 #H destruct
      lapply (ldrop_fwd_ldrop2 … HLK2) #HLK
      lapply (nta_lift h … HLK … HWU1 … HW) /2 width=4/ -HW
      elim (lift_total W2 0 (i+1)) #U2 #HWU2
      lapply (tpss_lift_ge … HW12 … HLK … HWU1 … HWU2) -HLK -HWU1 // #HU12
      lapply (cpr_tpss … HU12) -HU12 #HU12
      @(nta_conv … U2) /2 width=1/ /3 width=6/ (**) (* explicit constructor, /4 width=6/ is too slow *)
    | elim (lt_or_ge i (d + e)) #Hide [ -HWV1 | -IHWV1 -HW -Hdi ]
      [ elim (ltpss_ldrop_conf_be … HL12 … HLK1 ? ?) -L1 // /2 width=2/ #X #H #HLK2
        elim (ltpss_inv_tpss21 … H ?) -H /2 width=1/ -Hdi -Hide #K2 #W2 #HK12 #HW12 #H destruct
        lapply (ldrop_fwd_ldrop2 … HLK2) #HLK
        lapply (nta_lift h … HLK … HWU1 … HW) /2 width=4/ -HW
        elim (lift_total W2 0 (i+1)) #U2 #HWU2
        lapply (tpss_lift_ge … HW12 … HLK … HWU1 … HWU2) -HLK -HWU1 // #HU12
        lapply (cpr_tpss … HU12) -HU12 #HU12
        @(nta_conv … U2) /2 width=1/ /3 width=6/ (**) (* explicit constructor, /4 width=6/ is too slow *)
      | lapply (ltpss_ldrop_conf_ge … HL12 … HLK1 ?) -L1 // -Hide /2 width=6/
      ]
    ]
  | * #K2 #V2 #W2 #Hdi #Hide #HLK2 #_ #_
    elim (ltpss_ldrop_conf_be … HL12 … HLK1 ? ?) -L1 // /2 width=2/ #X #H #HL2K0
    elim (ltpss_inv_tpss21 … H ?) -H /2 width=1/ -Hdi -Hide #K0 #V0 #_ #_ #H destruct
    lapply (ldrop_mono … HL2K0 … HLK2) -HL2K0 -HLK2 #H destruct
  ]
| #I #L1 #V1 #W1 #T1 #U1 #_ #_ #IHVW1 #IHTU1 #L2 #d #e #HL12 #X #H
  elim (tpss_inv_bind1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct
  lapply (cpr_tpss … HV12) #HV
  lapply (IHTU1 (L2.ⓑ{I}V1) (d+1) e ? T1 ?) // /2 width=1/ #H
  elim (nta_fwd_correct … H) -H #U2 #HU12
  @(nta_conv … (ⓑ{I}V2.U1)) /3 width=2/ /3 width=4/ /4 width=4/ (**) (* explicit constructor, /5 width=6/ is too slow *)
| #L1 #V1 #W1 #T1 #U1 #_ #_ #IHVW1 #IHTU1 #L2 #d #e #HL12 #X #H
  elim (tpss_inv_flat1 … H) -H #V2 #Y #HV12 #HY #H destruct
  elim (tpss_inv_bind1 … HY) -HY #W2 #T2 #HW12 #HT12 #H destruct
  lapply (cpr_tpss … HV12) #HV
  lapply (IHTU1 L2 d e ? (ⓛW1.T1) ?) // #H
  elim (nta_fwd_correct … H) -H #X #H
  elim (nta_inv_bind1 … H) -H #W #U #HW #HU #_
  @(nta_conv … (ⓐV2.ⓛW1.U1)) /3 width=2/ /3 width=4/ /4 width=5/ (**) (* explicit constructor, /5 width=5/ is too slow *)
| #L1 #V1 #W1 #T1 #U1 #_ #_ #IHTU1 #IHUW1 #L2 #d #e #HL12 #X #H
  elim (tpss_inv_flat1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct
  lapply (cpr_tpss … HV12) #HV
  elim (nta_fwd_correct h L2 (ⓐV1.T1) (ⓐV1.U1) ?) [2: /3 width=4/ ] #U #HU
  @(nta_conv … (ⓐV2.U1)) // /3 width=1/ /4 width=5/ (**) (* explicit constructor, /5 width=5/ is too slow *)
| #L1 #T1 #U1 #W1 #_ #_ #IHTU1 #IHUW1 #L2 #d #e #HL12 #X #H
  elim (tpss_inv_flat1 … H) -H #U2 #T2 #HU12 #HT12 #H destruct
  lapply (cpr_tpss … HU12) /4 width=4/
| #L1 #T1 #U11 #U12 #U #_ #HU112 #_ #IHTU11 #IHU12 #L2 #d #e #HL12 #T2 #HT12
  @(nta_conv … U11) /2 width=5/ (**) (* explicot constructor, /3 width=7/ is too slow *)
]
qed.

lemma nta_ltpss_tps_conf: ∀h,L1,T1,U. ⦃h, L1⦄ ⊢ T1 : U →
                          ∀L2,d,e. L1 ▶* [d, e] L2 →
                          ∀T2. L2 ⊢ T1 ▶ [d, e] T2 → ⦃h, L2⦄ ⊢ T2 : U.
/3 width=7/ qed.

lemma nta_ltpss_conf: ∀h,L1,T,U. ⦃h, L1⦄ ⊢ T : U →
                      ∀L2,d,e. L1 ▶* [d, e] L2 → ⦃h, L2⦄ ⊢ T : U.
/2 width=7/ qed.

lemma nta_tpss_conf: ∀h,L,T1,U. ⦃h, L⦄ ⊢ T1 : U →
                     ∀T2,d,e. L ⊢ T1 ▶* [d, e] T2 → ⦃h, L⦄ ⊢ T2 : U.
/2 width=7/ qed.

lemma nta_tps_conf: ∀h,L,T1,U. ⦃h, L⦄ ⊢ T1 : U →
                    ∀T2,d,e. L ⊢ T1 ▶ [d, e] T2 → ⦃h, L⦄ ⊢ T2 : U.
/2 width=7/ qed.
