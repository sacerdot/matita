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

include "basic_2/unfold/ltpss_tpss.ma".
include "basic_2/unfold/ltpsss.ma".

(* ITERATED PARTIAL UNFOLD ON LOCAL ENVIRONMENTS ****************************)

(* Properties concerning partial substitution on terms **********************)

lemma ltpsss_tps2: ∀L1,L2,I,e.
                   L1 [0, e] ▶** L2 → ∀V1,V2. L2 ⊢ V1 [0, e] ▶ V2 →
                   L1. ⓑ{I} V1 [0, e + 1] ▶** L2. ⓑ{I} V2.
#L1 #L2 #I #e #H @(ltpsss_ind … H) -L2
[ /3 width=1/
| #L #L2 #_ #HL2 #IHL #V1 #V2 #HV12
  elim (ltpss_tps_trans … HV12 … HL2) -HV12 #V #HV1 #HV2
  lapply (IHL … HV1) -IHL -HV1 /3 width=5/
]
qed.

lemma ltpsss_tps2_lt: ∀L1,L2,I,V1,V2,e.
                      L1 [0, e - 1] ▶** L2 → L2 ⊢ V1 [0, e - 1] ▶ V2 →
                      0 < e → L1. ⓑ{I} V1 [0, e] ▶** L2. ⓑ{I} V2.
#L1 #L2 #I #V1 #V2 #e #HL12 #HV12 #He
>(plus_minus_m_m e 1) // /2 width=1/
qed.

lemma ltpsss_tps1: ∀L1,L2,I,d,e. L1 [d, e] ▶** L2 →
                   ∀V1,V2. L2 ⊢ V1 [d, e] ▶ V2 →
                   L1. ⓑ{I} V1 [d + 1, e] ▶** L2. ⓑ{I} V2.
#L1 #L2 #I #d #e #H @(ltpsss_ind … H) -L2
[ /3 width=1/
| #L #L2 #_ #HL2 #IHL #V1 #V2 #HV12
  elim (ltpss_tps_trans … HV12 … HL2) -HV12 #V #HV1 #HV2
  lapply (IHL … HV1) -IHL -HV1 /3 width=5/
]
qed.

lemma ltpsss_tps1_lt: ∀L1,L2,I,V1,V2,d,e.
                      L1 [d - 1, e] ▶** L2 → L2 ⊢ V1 [d - 1, e] ▶ V2 →
                      0 < d → L1. ⓑ{I} V1 [d, e] ▶** L2. ⓑ{I} V2.
#L1 #L2 #I #V1 #V2 #d #e #HL12 #HV12 #Hd
>(plus_minus_m_m d 1) // /2 width=1/
qed.

(* Properties concerning partial unfold on terms ****************************)

lemma ltpsss_tpss_conf_ge: ∀L0,L1,T2,U2,d1,e1,d2,e2. d1 + e1 ≤ d2 → 
                           L0 ⊢ T2 [d2, e2] ▶* U2 → L0 [d1, e1] ▶** L1 →
                           L1 ⊢ T2 [d2, e2] ▶* U2.
#L0 #L1 #T2 #U2 #d1 #e1 #d2 #e2 #Hde1d2 #HTU2 #H @(ltpsss_ind … H) -L1 //
-HTU2 #L #L1 #_ #HL1 #IHL
lapply (ltpss_tpss_conf_ge … IHL … HL1 ?) -HL1 -IHL //
qed.

lemma ltpsss_tpss_trans_ge: ∀L1,L0,d1,e1. L1 [d1, e1] ▶** L0 →
                            ∀T2,U2,d2,e2. L0 ⊢ T2 [d2, e2] ▶* U2 →
                            d1 + e1 ≤ d2 → L1 ⊢ T2 [d2, e2] ▶* U2.
#L1 #L0 #d1 #e1 #H @(ltpsss_ind … H) -L0 //
#L #L0 #_ #HL0 #IHL #T2 #U2 #d2 #e2 #HTU2 #Hde1d2
lapply (ltpss_tpss_trans_ge … HTU2 … HL0 ?) -HL0 -HTU2 // /2 width=1/
qed.
