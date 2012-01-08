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

include "Basic_2/unfold/tpss_ltps.ma".
include "Basic_2/unfold/ltpss.ma".

(* PARTIAL UNFOLD ON LOCAL ENVIRONMENTS *************************************)

(* Properties concerning partial unfold on terms ****************************)

lemma ltpss_tpss_trans_ge: ∀L1,L0,d1,e1. L1 [d1, e1] ▶* L0 →
                           ∀T2,U2,d2,e2. L0 ⊢ T2 [d2, e2] ▶* U2 →
                           d1 + e1 ≤ d2 → L1 ⊢ T2 [d2, e2] ▶* U2.
#L1 #L0 #d1 #e1 #H @(ltpss_ind … H) -L0 //
#L #L0 #_ #HL0 #IHL #T2 #U2 #d2 #e2 #HTU2 #Hde1d2
lapply (ltps_tpss_trans_ge … HL0 HTU2) -HL0 -HTU2 /2 width=1/
qed.

lemma ltpss_tps_trans_ge: ∀L1,L0,d1,e1. L1 [d1, e1] ▶* L0 →
                          ∀T2,U2,d2,e2. L0 ⊢ T2 [d2, e2] ▶ U2 →
                          d1 + e1 ≤ d2 → L1 ⊢ T2 [d2, e2] ▶* U2.
#L1 #L0 #d1 #e1 #HL10 #T2 #U2 #d2 #e2 #HTU2 #Hde1d2
@(ltpss_tpss_trans_ge … HL10 … Hde1d2) /2 width=1/ (**) (* /3 width=6/ is too slow *)
qed.

lemma ltpss_tpss_trans_eq: ∀L0,L1,d,e. L0 [d, e] ▶* L1 →
                           ∀T2,U2. L1 ⊢ T2 [d, e] ▶* U2 → L0 ⊢ T2 [d, e] ▶* U2.
#L0 #L1 #d #e #H @(ltpss_ind … H) -L1
[ /2 width=1/
| #L #L1 #_ #HL1 #IHL #T2 #U2 #HTU2
  lapply (ltps_tpss_trans_eq … HL1 HTU2) -HL1 -HTU2 /2 width=1/
]
qed.

lemma ltpss_tps_trans_eq: ∀L0,L1,d,e. L0 [d, e] ▶* L1 →
                          ∀T2,U2. L1 ⊢ T2 [d, e] ▶ U2 → L0 ⊢ T2 [d, e] ▶* U2.
/3 width=3/ qed.

lemma ltpss_tpss_conf_ge: ∀L0,L1,T2,U2,d1,e1,d2,e2. d1 + e1 ≤ d2 → 
                          L0 ⊢ T2 [d2, e2] ▶* U2 → L0 [d1, e1] ▶* L1 →
                          L1 ⊢ T2 [d2, e2] ▶* U2.
#L0 #L1 #T2 #U2 #d1 #e1 #d2 #e2 #Hde1d2 #HTU2 #H @(ltpss_ind … H) -L1
[ //
| -HTU2 #L #L1 #_ #HL1 #IHL
  lapply (ltps_tpss_conf_ge … HL1 IHL) -HL1 -IHL //
]
qed.

lemma ltpss_tps_conf_ge: ∀L0,L1,T2,U2,d1,e1,d2,e2. d1 + e1 ≤ d2 → 
                         L0 ⊢ T2 [d2, e2] ▶ U2 → L0 [d1, e1] ▶* L1 →
                         L1 ⊢ T2 [d2, e2] ▶* U2.
#L0 #L1 #T2 #U2 #d1 #e1 #d2 #e2 #Hde1d2 #HTU2 #HL01
@(ltpss_tpss_conf_ge … Hde1d2 … HL01) /2 width=1/ (**) (* /3 width=6/ is too slow *)
qed.

lemma ltpss_tpss_conf_eq: ∀L0,L1,T2,U2,d,e.
                          L0 ⊢ T2 [d, e] ▶* U2 → L0 [d, e] ▶* L1 →
                          ∃∃T. L1 ⊢ T2 [d, e] ▶* T & L1 ⊢ U2 [d, e] ▶* T.
#L0 #L1 #T2 #U2 #d #e #HTU2 #H @(ltpss_ind … H) -L1
[ /2 width=3/
| -HTU2 #L #L1 #_ #HL1 * #W2 #HTW2 #HUW2
  elim (ltps_tpss_conf … HL1 HTW2) -HTW2 #T #HT2 #HW2T
  elim (ltps_tpss_conf … HL1 HUW2) -HL1 -HUW2 #U #HU2 #HW2U
  elim (tpss_conf_eq … HW2T … HW2U) -HW2T -HW2U #V #HTV #HUV
  lapply (tpss_trans_eq … HT2 … HTV) -T
  lapply (tpss_trans_eq … HU2 … HUV) -U /2 width=3/
]
qed.

lemma ltpss_tps_conf_eq: ∀L0,L1,T2,U2,d,e.
                         L0 ⊢ T2 [d, e] ▶ U2 → L0 [d, e] ▶* L1 →
                         ∃∃T. L1 ⊢ T2 [d, e] ▶* T & L1 ⊢ U2 [d, e] ▶* T.
/3 width=3/ qed.

lemma ltpss_tpss_conf: ∀L1,T1,T2,d,e. L1 ⊢ T1 [d, e] ▶* T2 →
                       ∀L2,ds,es. L1 [ds, es] ▶* L2 → 
                       ∃∃T. L2 ⊢ T1 [d, e] ▶* T & L1 ⊢ T2 [ds, es] ▶* T.
#L1 #T1 #T2 #d #e #HT12 #L2 #ds #es #H @(ltpss_ind … H) -L2
[ /3 width=3/
| #L #L2 #HL1 #HL2 * #T #HT1 #HT2
  elim (ltps_tpss_conf … HL2 HT1) -HT1 #T0 #HT10 #HT0
  lapply (ltps_tpss_trans_eq … HL2 … HT0) -HL2 -HT0 #HT0
  lapply (ltpss_tpss_trans_eq … HL1 … HT0) -HL1 -HT0 #HT0
  lapply (tpss_trans_eq … HT2 … HT0) -T /2 width=3/
]
qed.

lemma ltpss_tps_conf: ∀L1,T1,T2,d,e. L1 ⊢ T1 [d, e] ▶ T2 →
                      ∀L2,ds,es. L1 [ds, es] ▶* L2 → 
                      ∃∃T. L2 ⊢ T1 [d, e] ▶* T & L1 ⊢ T2 [ds, es] ▶* T.
/3 width=1/ qed.

(* Advanced properties ******************************************************)

lemma ltpss_tps2: ∀L1,L2,I,e.
                  L1 [0, e] ▶* L2 → ∀V1,V2. L2 ⊢ V1 [0, e] ▶ V2 →
                  L1. 𝕓{I} V1 [0, e + 1] ▶* L2. 𝕓{I} V2.
#L1 #L2 #I #e #H @(ltpss_ind … H) -L2
[ /3 width=1/
| #L #L2 #_ #HL2 #IHL #V1 #V2 #HV12
  elim (ltps_tps_trans … HV12 … HL2) -HV12 #V #HV1 #HV2
  lapply (IHL … HV1) -IHL -HV1 #HL1
  @step /2 width=5/ (**) (* /3 width=5/ is too slow *)
]
qed.

lemma ltpss_tps2_lt: ∀L1,L2,I,V1,V2,e.
                     L1 [0, e - 1] ▶* L2 → L2 ⊢ V1 [0, e - 1] ▶ V2 →
                     0 < e → L1. 𝕓{I} V1 [0, e] ▶* L2. 𝕓{I} V2.
#L1 #L2 #I #V1 #V2 #e #HL12 #HV12 #He
>(plus_minus_m_m e 1) // /2 width=1/
qed.

lemma ltpss_tps1: ∀L1,L2,I,d,e. L1 [d, e] ▶* L2 →
                  ∀V1,V2. L2 ⊢ V1 [d, e] ▶ V2 →
                  L1. 𝕓{I} V1 [d + 1, e] ▶* L2. 𝕓{I} V2.
#L1 #L2 #I #d #e #H @(ltpss_ind … H) -L2
[ /3 width=1/
| #L #L2 #_ #HL2 #IHL #V1 #V2 #HV12
  elim (ltps_tps_trans … HV12 … HL2) -HV12 #V #HV1 #HV2
  lapply (IHL … HV1) -IHL -HV1 #HL1
  @step /2 width=5/ (**) (* /3 width=5/ is too slow *)
]
qed.

lemma ltpss_tps1_lt: ∀L1,L2,I,V1,V2,d,e.
                     L1 [d - 1, e] ▶* L2 → L2 ⊢ V1 [d - 1, e] ▶ V2 →
                     0 < d → L1. 𝕓{I} V1 [d, e] ▶* L2. 𝕓{I} V2.
#L1 #L2 #I #V1 #V2 #d #e #HL12 #HV12 #Hd
>(plus_minus_m_m d 1) // /2 width=1/
qed.

(* Advanced forward lemmas **************************************************)

lemma ltpss_fwd_tpss21: ∀e,K1,I,V1,L2. 0 < e → K1. 𝕓{I} V1 [0, e] ▶* L2 →
                        ∃∃K2,V2. K1 [0, e - 1] ▶* K2 & K1 ⊢ V1 [0, e - 1] ▶* V2 &
                                 L2 = K2. 𝕓{I} V2.
#e #K1 #I #V1 #L2 #He #H @(ltpss_ind … H) -L2
[ /2 width=5/
| #L #L2 #_ #HL2 * #K #V #HK1 #HV1 #H destruct
  elim (ltps_inv_tps21 … HL2 ?) -HL2 // #K2 #V2 #HK2 #HV2 #H
  lapply (ltps_tps_trans_eq … HV2 … HK2) -HV2 #HV2
  lapply (ltpss_tpss_trans_eq … HK1 … HV2) -HV2 #HV2 /3 width=5/
]
qed-.

lemma ltpss_fwd_tpss11: ∀d,e,I,K1,V1,L2. 0 < d → K1. 𝕓{I} V1 [d, e] ▶* L2 →
                        ∃∃K2,V2. K1 [d - 1, e] ▶* K2 &
                                 K1 ⊢ V1 [d - 1, e] ▶* V2 &
                                 L2 = K2. 𝕓{I} V2.
#d #e #K1 #I #V1 #L2 #Hd #H @(ltpss_ind … H) -L2
[ /2 width=5/
| #L #L2 #_ #HL2 * #K #V #HK1 #HV1 #H destruct
  elim (ltps_inv_tps11 … HL2 ?) -HL2 // #K2 #V2 #HK2 #HV2 #H
  lapply (ltps_tps_trans_eq … HV2 … HK2) -HV2 #HV2
  lapply (ltpss_tpss_trans_eq … HK1 … HV2) -HV2 #HV2 /3 width=5/
]
qed-.
