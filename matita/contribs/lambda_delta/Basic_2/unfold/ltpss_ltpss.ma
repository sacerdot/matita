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

include "Basic_2/unfold/ltpss_tpss.ma".

(* PARTIAL UNFOLD ON LOCAL ENVIRONMENTS *************************************)

(* Main properties **********************************************************)

theorem ltpss_trans_eq: ∀L1,L,L2,d,e.
                        L1 [d, e] ≫* L → L [d, e] ≫* L2 → L1 [d, e] ≫* L2. 
/2 width=3/ qed.

lemma ltpss_tpss2: ∀L1,L2,I,V1,V2,e.
                   L1 [0, e] ≫* L2 → L2 ⊢ V1 [0, e] ≫* V2 →
                   L1. 𝕓{I} V1 [0, e + 1] ≫* L2. 𝕓{I} V2.
#L1 #L2 #I #V1 #V2 #e #HL12 #H @(tpss_ind … H) -V2
[ /2 width=1/
| #V #V2 #_ #HV2 #IHV @(ltpss_trans_eq … IHV) /2 width=1/
]
qed.

lemma ltpss_tpss2_lt: ∀L1,L2,I,V1,V2,e.
                      L1 [0, e - 1] ≫* L2 → L2 ⊢ V1 [0, e - 1] ≫* V2 →
                      0 < e → L1. 𝕓{I} V1 [0, e] ≫* L2. 𝕓{I} V2.
#L1 #L2 #I #V1 #V2 #e #HL12 #HV12 #He
>(plus_minus_m_m e 1) // /2 width=1/
qed.

lemma ltpss_tpss1: ∀L1,L2,I,V1,V2,d,e.
                   L1 [d, e] ≫* L2 → L2 ⊢ V1 [d, e] ≫* V2 →
                   L1. 𝕓{I} V1 [d + 1, e] ≫* L2. 𝕓{I} V2.
#L1 #L2 #I #V1 #V2 #d #e #HL12 #H @(tpss_ind … H) -V2
[ /2 width=1/
| #V #V2 #_ #HV2 #IHV @(ltpss_trans_eq … IHV) /2 width=1/
]
qed.

lemma ltpss_tpss1_lt: ∀L1,L2,I,V1,V2,d,e.
                      L1 [d - 1, e] ≫* L2 → L2 ⊢ V1 [d - 1, e] ≫* V2 →
                      0 < d → L1. 𝕓{I} V1 [d, e] ≫* L2. 𝕓{I} V2.
#L1 #L2 #I #V1 #V2 #d #e #HL12 #HV12 #Hd
>(plus_minus_m_m d 1) // /2 width=1/
qed.
