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

include "basic_2/dynamic/nta_ltpss.ma".
include "basic_2/dynamic/nta_thin.ma".
include "basic_2/dynamic/lsubn_nta.ma".

lemma cpr_beta: ∀L,V1,V2,W,T1,T2.
                V1 ➡ V2 → L.ⓛW ⊢ T1 ➡ T2 → L ⊢ ⓐV1.ⓛW.T1 ➡ ⓓV2.T2.
#L #V1 #V2 #W #T1 #T2 #HV12 * #T #HT1 #HT2
lapply (tpss_inv_S2 … HT2 L W ?) -HT2 // #HT2
lapply (tpss_lsubs_trans … HT2 (L.ⓓV2) ?) -HT2 /2 width=1/ #HT2
@(ex2_1_intro … (ⓓV2.T)) /2 width=1/ (**) (* explicit constructor, /3/ is too skow *)
qed.

lemma cpr_beta2: ∀L,V1,V2,W,T1,T2.
                 L ⊢ V1 ➡ V2 → L.ⓛW ⊢ T1 ➡ T2 → L ⊢ ⓐV1.ⓛW.T1 ➡ ⓓV2.T2.
#L #V1 #V2 #W #T1 #T2 * #V #HV1 #HV2 * #T #HT1 #HT2
lapply (tpss_inv_S2 … HT2 L W ?) -HT2 // #HT2
lapply (tpss_lsubs_trans … HT2 (L.ⓓV2) ?) -HT2 /2 width=1/ #HT2
@(ex2_1_intro … (ⓓV.T)) /2 width=1/ (**) (* explicit constructor, /3/ is too skow *)
qed.

(* NATIVE TYPE ASSIGNMENT ON TERMS ******************************************)

(* Properties on context-free parallel reduction for local environments ******)

lemma nta_ltpr_tpr_conf: ∀h,L1,T1,U. ⦃h, L1⦄ ⊢ T1 : U → ∀L2. L1 ➡ L2 →
                         ∀T2. T1 ➡ T2 → ⦃h, L2⦄ ⊢ T2 : U.
#h #L1 #T1 #U #H @(nta_ind_alt … H) -L1 -T1 -U
[ #L1 #k #L2 #_ #T2 #H
  >(tpr_inv_atom1 … H) -H //
| #L1 #K1 #V1 #W #U #i #HLK1 #_ #HWU #IHV1 #L2 #HL12 #T2 #H
  >(tpr_inv_atom1 … H) -T2
  elim (ltpr_ldrop_conf … HLK1 … HL12) -HLK1 -HL12 #X #HLK2 #H
  elim (ltpr_inv_pair1 … H) -H #K2 #V2 #HK12 #HV12 #H destruct /3 width=6/
| #L1 #K1 #W1 #V1 #U1 #i #HLK1 #HWV1 #HWU1 #IHWV1 #L2 #HL12 #T2 #H
  >(tpr_inv_atom1 … H) -T2
  elim (ltpr_ldrop_conf … HLK1 … HL12) -HLK1 -HL12 #X #HLK2 #H
  elim (ltpr_inv_pair1 … H) -H #K2 #W2 #HK12 #HW12 #H destruct
  lapply (ldrop_fwd_ldrop2 … HLK2) #HLK
  elim (lift_total V1 0 (i+1)) #W #HW
  lapply (nta_lift h … HLK … HWU1 … HW) /2 width=1/ -HLK -HW
  elim (lift_total W2 0 (i+1)) #U2 #HWU2
  lapply (tpr_lift … HW12 … HWU1 … HWU2) -HWU1 #HU12
  @(nta_conv … U2) /2 width=1/ /3 width=6/ (**) (* explicit constructor, /3 width=6/ is too slow *)
| #I #L1 #V1 #W1 #T1 #U1 #_ #_ #IHVW1 #IHTU1 #L2 #HL12 #X #H
  elim (tpr_inv_bind1 … H) -H *
  [ #V2 #T0 #T2 #HV12 #HT10 #HT02 #H destruct
    lapply (IHVW1 … HL12 … HV12) #HV2W1
    lapply (IHVW1 L2 … V1 ?) // -IHVW1 #HWV1
    lapply (IHTU1 (L2.ⓑ{I}V2) … HT10) -HT10 /2 width=1/ #HT0U1
    lapply (IHTU1 (L2.ⓑ{I}V1) ? T1 ?) -IHTU1 // /2 width=1/ -HL12 #H
    lapply (tps_lsubs_trans … HT02 (L2.ⓑ{I}V2) ?) -HT02 /2 width=1/ #HT02
    lapply (nta_tps_conf … HT0U1 … HT02) -T0 #HT2U1
    elim (nta_fwd_correct … H) -H #U2 #HU12
    @(nta_conv … (ⓑ{I}V2.U1)) /2 width=2/ /3 width=1/ (**) (* explicit constructor, /4 width=6/ is too slow *)
  | #T #HT1 #HTX #H destruct
    lapply (IHVW1 … HL12 V1 ?) -IHVW1 // #HVW1
    elim (lift_total X 0 1) #Y #HXY
    lapply (tpr_lift … HTX … HT1 … HXY) -T #H
    lapply (IHTU1 (L2.ⓓV1) … H) -T1 /2 width=1/ -L1 #H
    elim (nta_fwd_correct … H) #T1 #HUT1
    elim (nta_thin_conf … H L2 0 (0+1) ? ?) -H /2 width=1/ /3 width=1/ #T #U #HTU #H
    normalize in ⊢ (??%??? → ?); #HU1
    lapply (delift_inv_lift1_eq … H L2 … HXY) -Y /2 width=1/ #H destruct
    @(nta_conv … U) // /2 width=2/
  ]
| #L1 #V1 #W1 #T1 #U1 #_ #_ #IHVW1 #IHTU1 #L2 #HL12 #X #H
  elim (tpr_inv_appl1 … H) -H *
  [ #V2 #Y #HV12 #HY #H destruct
    elim (tpr_inv_abst1 … HY) -HY #W2 #T2 #HW12 #HT12 #H destruct
    lapply (IHTU1 L2 ? (ⓛW1.T1) ?) // #H
    elim (nta_fwd_correct … H) -H #X #H
    elim (nta_inv_bind1 … H) -H #W #U #HW #HU #_
    @(nta_conv … (ⓐV2.ⓛW1.U1)) /4 width=2/ (**) (* explicit constructor, /5 width=5/ is too slow *)
  | #V2 #W2 #T0 #T2 #HV12 #HT02 #H1 #H2 destruct
    lapply (IHVW1 … HL12 … HV12) #HVW2
    lapply (IHVW1 … HL12 V1 ?) -IHVW1 // #HV1W2
    lapply (IHTU1 … HL12 (ⓛW2.T2) ?) -IHTU1 -HL12 /2 width=1/ -HT02 #H1
    elim (nta_fwd_correct … H1) #T #H2
    elim (nta_inv_bind1 … H1) -H1 #W #U2 #HW2 #HTU2 #H
    elim (cpcs_inv_abst … H Abst W2) -H #_ #HU21
    elim (nta_inv_bind1 … H2) -H2 #W0 #U0 #_ #H #_ -T -W0 
    lapply (lsubn_nta_trans … HTU2 (L2.ⓓV2) ?) -HTU2 /2 width=1/ #HTU2
    @(nta_conv … (ⓓV2.U2))
    [2: /2 width=2/
    |3: -h -L1 -T0 -T2 -W -U0
    |4: /3 width=2/ 
    ]
  | #V0 #V2 #W0 #W2 #T0 #T2 #_ #_ #_ #_ #H destruct
  ]





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



















fact nta_ltpr_tpr_conf_aux: ∀h,L,T,L1,T1,U. ⦃h, L1⦄ ⊢ T1 : U → L = L1 → T = T1 →
                            ∀L2. L1 ➡ L2 → ∀T2. T1 ➡ T2 → ⦃h, L2⦄ ⊢ T2 : U.
  
  
| #L1 #V1 #T1 #B #A #HV1 #HT1 #H1 #H2 #L2 #HL12 #X #H destruct
  elim (tpr_inv_appl1 … H) -H *
  [ #V2 #T2 #HV12 #HT12 #H destruct
    lapply (IH … HV1 … HL12 … HV12) -HV1 -HV12 /width=5/ #HB
    lapply (IH … HT1 … HL12 … HT12) -IH -HT1 -HL12 -HT12 /width=5/ /2 width=3/
  | #V2 #W2 #T0 #T2 #HV12 #HT02 #H1 #H2 destruct
    elim (nta_inv_abst … HT1) -HT1 #B0 #A0 #HB0 #HA0 #H destruct
    lapply (IH … HV1 … HL12 … HV12) -HV1 -HV12 /width=5/ #HB
    lapply (IH … HB0  … HL12 W2 ?) -HB0 /width=5/ #HB0
    lapply (IH … HA0 … (L2.ⓛW2) … HT02) -IH -HA0 -HT02 /width=5/ -T0 /2 width=1/ -L1 -V1 /4 width=7/
  | #V0 #V2 #W0 #W2 #T0 #T2 #HV10 #HW02 #HT02 #HV02 #H1 #H2 destruct
    elim (nta_inv_abbr … HT1) -HT1 #B0 #HW0 #HT0
    lapply (IH … HW0  … HL12 … HW02) -HW0 /width=5/ #HW2
    lapply (IH … HV1 … HL12 … HV10) -HV1 -HV10 /width=5/ #HV0
    lapply (IH … HT0 … (L2.ⓓW2) … HT02) -IH -HT0 -HT02 /width=5/ -V1 -T0 /2 width=1/ -L1 -W0 #HT2
    @(nta_abbr … HW2) -HW2
    @(nta_appl … HT2) -HT2 /3 width=7/ (**) (* explict constructors, /5 width=7/ is too slow *)
  ]
| #L1 #V1 #T1 #A #HV1 #HT1 #H1 #H2 #L2 #HL12 #X #H destruct
  elim (tpr_inv_cast1 … H) -H
  [ * #V2 #T2 #HV12 #HT12 #H destruct
    lapply (IH … HV1 … HL12 … HV12) -HV1 -HV12 /width=5/ #HV2
    lapply (IH … HT1 … HL12 … HT12) -IH -HT1 -HL12 -HT12 /width=5/ -L1 -V1 -T1 /2 width=1/
  | -HV1 #HT1X
     lapply (IH … HT1 … HL12 … HT1X) -IH -HT1 -HL12 -HT1X /width=5/
  ]
]
qed.

/2 width=9/ qed.

lemma nta_ltpr_conf: ∀L1,T,A. L1 ⊢ T : A → ∀L2. L1 ➡ L2 → L2 ⊢ T : A.
/2 width=5/ qed.

lemma nta_tpr_conf: ∀L,T1,A. L ⊢ T1 : A → ∀T2. T1 ➡ T2 → L ⊢ T2 : A.
/2 width=5/ qed.
