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

include "basic_2/unfold/ltpss_dx_ltpss_dx.ma".
include "basic_2/reducibility/ltpr_tps.ma".

(* CONTEXT-FREE PARALLEL REDUCTION ON LOCAL ENVIRONMENTS ********************)

(* Properties on partial unfold for terms ***********************************)

(* Basic_1: was: pr0_subst1 *)
lemma ltpr_tpr_tps_conf: ∀T1,T2. T1 ➡ T2 →
                         ∀L1,d,e,U1. L1 ⊢ T1 ▶ [d, e] U1 →
                         ∀L2. L1 ➡ L2 →
                         ∃∃U2. U1 ➡ U2 & L2 ⊢ T2 ▶* [d, e] U2.
#T1 #T2 #H elim H -T1 -T2
[ #I #L1 #d #e #U1 #H #L2 #HL12
  elim (ltpr_tps_conf … H … HL12) -L1 /3 width=3/
| #I #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #L1 #d #e #X #H #L2 #HL12
  elim (tps_inv_flat1 … H) -H #W1 #U1 #HVW1 #HTU1 #H destruct
  elim (IHV12 … HVW1 … HL12) -V1
  elim (IHT12 … HTU1 … HL12) -T1 -HL12 /3 width=5/
| #a #V1 #V2 #W #T1 #T2 #_ #_ #IHV12 #IHT12 #L1 #d #e #X #H #L2 #HL12
  elim (tps_inv_flat1 … H) -H #VV1 #Y #HVV1 #HY #HX destruct
  elim (tps_inv_bind1 … HY) -HY #WW #TT1 #_ #HTT1 #H destruct
  elim (IHV12 … HVV1 … HL12) -V1 #VV2 #HVV12 #HVV2
  elim (IHT12 … HTT1 (L2. ⓛWW) ?) -T1 /2 width=1/ -HL12 #TT2 #HTT12 #HTT2
  lapply (tpss_lsubr_trans … HTT2 (L2. ⓓVV2) ?) -HTT2 /3 width=5/
| #a #I #V1 #V2 #T1 #T #T2 #HV12 #_ #HT2 #IHV12 #IHT1 #L1 #d #e #X #H #L2 #HL12
  elim (tps_inv_bind1 … H) -H #W1 #U1 #HVW1 #HTU1 #H destruct
  elim (IHV12 … HVW1 … HL12) -V1 #W2 #HW12 #HVW2
  elim (IHT1 … HTU1 (L2. ⓑ{I} W2) ?) -T1 /2 width=1/ -HL12 #U #HU1 #HTU
  elim (tpss_strip_neq … HTU … HT2 ?) -T /2 width=1/ #U2 #HU2 #HTU2
  lapply (tps_lsubr_trans … HU2 (L2. ⓑ{I} V2) ?) -HU2 /2 width=1/ #HU2
  elim (ltpss_dx_tps_conf … HU2 (L2. ⓑ{I} W2) (d + 1) e ?) -HU2 /2 width=1/ #U3 #HU3 #HU23
  lapply (tps_lsubr_trans … HU3 (⋆. ⓑ{I} W2) ?) -HU3 /2 width=1/ #HU3
  lapply (tpss_lsubr_trans … HU23 (L2. ⓑ{I} W2) ?) -HU23 /2 width=1/ #HU23
  lapply (tpss_trans_eq … HTU2 … HU23) -U2 /3 width=5/
| #a #V #V1 #V2 #W1 #W2 #T1 #T2 #_ #HV2 #_ #_ #IHV12 #IHW12 #IHT12 #L1 #d #e #X #H #L2 #HL12
  elim (tps_inv_flat1 … H) -H #VV1 #Y #HVV1 #HY #HX destruct
  elim (tps_inv_bind1 … HY) -HY #WW1 #TT1 #HWW1 #HTT1 #H destruct
  elim (IHV12 … HVV1 … HL12) -V1 #VV2 #HVV12 #HVV2
  elim (IHW12 … HWW1 … HL12) -W1 #WW2 #HWW12 #HWW2
  elim (IHT12 … HTT1 (L2. ⓓWW2) ?) -T1 /2 width=1/ -HL12 #TT2 #HTT12 #HTT2
  elim (lift_total VV2 0 1) #VV #H2VV
  lapply (tpss_lift_ge … HVV2 (L2. ⓓWW2) … HV2 … H2VV) -V2 /2 width=1/ #HVV
  @ex2_intro [2: @tpr_theta |1: skip |3: @tpss_bind [2: @tpss_flat ] ] /width=11/ (**) (* /4 width=11/ is too slow *)
| #V #T1 #T #T2 #_ #HT2 #IHT1 #L1 #d #e #X #H #L2 #HL12
  elim (tps_inv_bind1 … H) -H #W #U1 #_ #HTU1 #H destruct -V
  elim (IHT1 … HTU1 (L2.ⓓW) ?) -T1 /2 width=1/ -HL12 #U #HU1 #HTU
  elim (tpss_inv_lift1_ge … HTU L2 … HT2 ?) -T <minus_plus_m_m /3 width=3/
| #V1 #T1 #T2 #_ #IHT12 #L1 #d #e #X #H #L2 #HL12
  elim (tps_inv_flat1 … H) -H #VV1 #TT1 #HVV1 #HTT1 #H destruct
  elim (IHT12 … HTT1 … HL12) -T1 -HL12 /3 width=3/
]
qed-.

lemma tpr_tps_conf_bind: ∀I,V1,V2,T1,T2,U1. V1 ➡ V2 → T1 ➡ T2 →
                         ⋆. ⓑ{I} V1 ⊢ T1 ▶ [0, 1] U1 →
                         ∃∃U2. U1 ➡ U2 & ⋆. ⓑ{I} V2 ⊢ T2 ▶ [0, 1] U2.
#I #V1 #V2 #T1 #T2 #U1 #HV12 #HT12 #HTU1
elim (ltpr_tpr_tps_conf … HT12 … HTU1 (⋆. ⓑ{I} V2) ?) -T1 /2 width=1/ -V1 #U2 #HU12 #HTU2
lapply (tpss_inv_SO2 … HTU2) -HTU2 /2 width=3/
qed-.

lemma ltpr_tpr_tpss_conf: ∀L1,L2. L1 ➡ L2 → ∀T1,T2. T1 ➡ T2 →
                          ∀d,e,U1. L1 ⊢ T1 ▶* [d, e] U1 →
                          ∃∃U2. U1 ➡ U2 & L2 ⊢ T2 ▶* [d, e] U2.
#L1 #L2 #HL12 #T1 #T2 #HT12 #d #e #U1 #HTU1 @(tpss_ind … HTU1) -U1
[ /2 width=3/
| -HT12 #U #U1 #_ #HU1 * #T #HUT #HT2
  elim (ltpr_tpr_tps_conf … HUT … HU1 … HL12) -U -HL12 #U2 #HU12 #HTU2
  lapply (tpss_trans_eq … HT2 … HTU2) -T /2 width=3/
]
qed-.

lemma tpr_tpss_conf: ∀T1,T2. T1 ➡ T2 →
                     ∀L,U1,d,e. L ⊢ T1 ▶* [d, e] U1 →
                     ∃∃U2. U1 ➡ U2 & L ⊢ T2 ▶* [d, e] U2.
/2 width=5 by ltpr_tpr_tpss_conf/ qed-.
