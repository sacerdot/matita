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

include "basic_2/unfold/ltpss_ltpss.ma".
include "basic_2/reducibility/ltpr_ldrop.ma".

(* CONTEXT-FREE PARALLEL REDUCTION ON TERMS *********************************)

(* Unfold properties ********************************************************)

(* Basic_1: was: pr0_subst1 *)
lemma tpr_tps_ltpr: ∀T1,T2. T1 ➡ T2 →
                    ∀L1,d,e,U1. L1 ⊢ T1 ▶ [d, e] U1 →
                    ∀L2. L1 ➡ L2 →
                    ∃∃U2. U1 ➡ U2 & L2 ⊢ T2 ▶* [d, e] U2.
#T1 #T2 #H elim H -T1 -T2
[ #I #L1 #d #e #X #H
  elim (tps_inv_atom1 … H) -H
  [ #H destruct /2 width=3/
  | * #K1 #V1 #i #Hdi #Hide #HLK1 #HVU1 #H #L2 #HL12 destruct
    elim (ltpr_ldrop_conf … HLK1 … HL12) -L1 #X #HLK2 #H
    elim (ltpr_inv_pair1 … H) -H #K2 #V2 #_ #HV12 #H destruct
    elim (lift_total V2 0 (i+1)) #U2 #HVU2
    lapply (tpr_lift … HV12 … HVU1 … HVU2) -V1 #HU12
    @ex2_1_intro [2: @HU12 | skip | /3 width=4/ ] (**) (* /4 width=6/ is too slow *)
  ]
| #I #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #L1 #d #e #X #H #L2 #HL12
  elim (tps_inv_flat1 … H) -H #W1 #U1 #HVW1 #HTU1 #H destruct
  elim (IHV12 … HVW1 … HL12) -V1
  elim (IHT12 … HTU1 … HL12) -T1 -HL12 /3 width=5/
| #V1 #V2 #W #T1 #T2 #_ #_ #IHV12 #IHT12 #L1 #d #e #X #H #L2 #HL12
  elim (tps_inv_flat1 … H) -H #VV1 #Y #HVV1 #HY #HX destruct
  elim (tps_inv_bind1 … HY) -HY #WW #TT1 #_ #HTT1 #H destruct
  elim (IHV12 … HVV1 … HL12) -V1 #VV2 #HVV12 #HVV2
  elim (IHT12 … HTT1 (L2. ⓛWW) ?) -T1 /2 width=1/ -HL12 #TT2 #HTT12 #HTT2
  lapply (tpss_lsubs_trans … HTT2 (L2. ⓓVV2) ?) -HTT2 /3 width=5/
| #I #V1 #V2 #T1 #T2 #U2 #HV12 #_ #HTU2 #IHV12 #IHT12 #L1 #d #e #X #H #L2 #HL12
  elim (tps_inv_bind1 … H) -H #VV1 #TT1 #HVV1 #HTT1 #H destruct
  elim (IHV12 … HVV1 … HL12) -V1 #VV2 #HVV12 #HVV2
  elim (IHT12 … HTT1 (L2. ⓑ{I} VV2) ?) -T1 /2 width=1/ -HL12 #TT2 #HTT12 #HTT2
  elim (tpss_strip_neq … HTT2 … HTU2 ?) -T2 /2 width=1/ #T2 #HTT2 #HUT2
  lapply (tps_lsubs_trans … HTT2 (L2. ⓑ{I} V2) ?) -HTT2 /2 width=1/ #HTT2
  elim (ltpss_tps_conf … HTT2 (L2. ⓑ{I} VV2) (d + 1) e ?) -HTT2 /2 width=1/ #W2 #HTTW2 #HTW2
  lapply (tps_lsubs_trans … HTTW2 (⋆. ⓑ{I} VV2) ?) -HTTW2 /2 width=1/ #HTTW2
  lapply (tpss_lsubs_trans … HTW2 (L2. ⓑ{I} VV2) ?) -HTW2 /2 width=1/ #HTW2
  lapply (tpss_trans_eq … HUT2 … HTW2) -T2 /3 width=5/
| #V #V1 #V2 #W1 #W2 #T1 #T2 #_ #HV2 #_ #_ #IHV12 #IHW12 #IHT12 #L1 #d #e #X #H #L2 #HL12
  elim (tps_inv_flat1 … H) -H #VV1 #Y #HVV1 #HY #HX destruct
  elim (tps_inv_bind1 … HY) -HY #WW1 #TT1 #HWW1 #HTT1 #H destruct
  elim (IHV12 … HVV1 … HL12) -V1 #VV2 #HVV12 #HVV2
  elim (IHW12 … HWW1 … HL12) -W1 #WW2 #HWW12 #HWW2
  elim (IHT12 … HTT1 (L2. ⓓWW2) ?) -T1 /2 width=1/ -HL12 #TT2 #HTT12 #HTT2
  elim (lift_total VV2 0 1) #VV #H2VV
  lapply (tpss_lift_ge … HVV2 (L2. ⓓWW2) … HV2 … H2VV) -V2 /2 width=1/ #HVV
  @ex2_1_intro [2: @tpr_theta |1: skip |3: @tpss_bind [2: @tpss_flat ] ] /width=11/ (**) (* /4 width=11/ is too slow *)
| #V1 #TT1 #T1 #T2 #HTT1 #_ #IHT12 #L1 #d #e #X #H #L2 #HL12
  elim (tps_inv_bind1 … H) -H #V2 #TT2 #HV12 #HTT12 #H destruct
  elim (tps_inv_lift1_ge … HTT12 L1 … HTT1 ?) -TT1 /2 width=1/ #T2 #HT12 #HTT2
  elim (IHT12 … HT12 … HL12) -T1 -HL12 <minus_plus_m_m /3 width=3/
| #V1 #T1 #T2 #_ #IHT12 #L1 #d #e #X #H #L2 #HL12
  elim (tps_inv_flat1 … H) -H #VV1 #TT1 #HVV1 #HTT1 #H destruct
  elim (IHT12 … HTT1 … HL12) -T1 -HL12 /3 width=3/
]
qed.

lemma tpr_tps_bind: ∀I,V1,V2,T1,T2,U1. V1 ➡ V2 → T1 ➡ T2 →
                    ⋆. ⓑ{I} V1 ⊢ T1 ▶ [0, 1] U1 →
                    ∃∃U2. U1 ➡ U2 & ⋆. ⓑ{I} V2 ⊢ T2 ▶ [0, 1] U2.
#I #V1 #V2 #T1 #T2 #U1 #HV12 #HT12 #HTU1
elim (tpr_tps_ltpr … HT12 … HTU1 (⋆. ⓑ{I} V2) ?) -T1 /2 width=1/ /3 width=3/
qed.

lemma tpr_tpss_ltpr: ∀L1,L2. L1 ➡ L2 → ∀T1,T2. T1 ➡ T2 →
                     ∀d,e,U1. L1 ⊢ T1 ▶* [d, e] U1 →
                     ∃∃U2. U1 ➡ U2 & L2 ⊢ T2 ▶* [d, e] U2.
#L1 #L2 #HL12 #T1 #T2 #HT12 #d #e #U1 #HTU1 @(tpss_ind … HTU1) -U1
[ /2 width=3/
| -HT12 #U #U1 #_ #HU1 * #T #HUT #HT2
  elim (tpr_tps_ltpr … HUT … HU1 … HL12) -U -HL12 #U2 #HU12 #HTU2
  lapply (tpss_trans_eq … HT2 … HTU2) -T /2 width=3/
]
qed.

lemma tpr_tpss_conf: ∀T1,T2. T1 ➡ T2 →
                     ∀L,U1,d,e. L ⊢ T1 ▶* [d, e] U1 →
                     ∃∃U2. U1 ➡ U2 & L ⊢ T2 ▶* [d, e] U2.
/2 width=5/ qed. 
