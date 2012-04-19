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
include "basic_2/unfold/ltpsss_tpss.ma".

(* ITERATED PARTIAL UNFOLD ON LOCAL ENVIRONMENTS ****************************)

(* Advanced properties ******************************************************)

lemma ltpsss_strip: ∀L0,L1,d1,e1. L0 [d1, e1] ▶** L1 →
                    ∀L2,d2,e2. L0 [d2, e2] ▶* L2 →
                    ∃∃L. L1 [d2, e2] ▶* L & L2 [d1, e1] ▶** L.
/3 width=3/ qed.

lemma ltpsss_tpss_trans_eq: ∀L0,L1,d,e. L0 [d, e] ▶** L1 →
                            ∀T2,U2. L1 ⊢ T2 [d, e] ▶* U2 → L0 ⊢ T2 [d, e] ▶* U2.
#L0 #L1 #d #e #H @(ltpsss_ind … H) -L1
[ /2 width=1/
| #L #L1 #_ #HL1 #IHL #T2 #U2 #HTU2
  lapply (ltpss_tpss_trans_eq … HTU2 … HL1) -HL1 -HTU2 /2 width=1/
]
qed.

lemma ltpsss_tps_trans_eq: ∀L0,L1,d,e. L0 [d, e] ▶** L1 →
                           ∀T2,U2. L1 ⊢ T2 [d, e] ▶ U2 → L0 ⊢ T2 [d, e] ▶* U2.
/3 width=3/ qed.

lemma ltpsss_tpss_conf: ∀L1,T1,T2,d,e. L1 ⊢ T1 [d, e] ▶* T2 →
                        ∀L2,ds,es. L1 [ds, es] ▶** L2 →
                        ∃∃T. L2 ⊢ T1 [d, e] ▶* T & L1 ⊢ T2 [ds, es] ▶* T.
#L1 #T1 #T2 #d #e #HT12 #L2 #ds #es #H @(ltpsss_ind … H) -L2
[ /2 width=3/
| -HT12 #L #L2 #HL1 #HL2 * #T #HT1 #HT2
  lapply (ltpsss_strap1 … HL1 HL2) -HL1 #HL12
  elim (ltpss_tpss_conf … HT1 … HL2) -L #T0 #HT10 #HT0
  lapply (ltpsss_tpss_trans_eq … HL12 … HT0) -HL12 -HT0 #HT0
  lapply (tpss_trans_eq … HT2 HT0) -T /2 width=3/
]
qed.

lemma ltpsss_tps_conf: ∀L1,T1,T2,d,e. L1 ⊢ T1 [d, e] ▶ T2 →
                       ∀L2,ds,es. L1 [ds, es] ▶** L2 → 
                       ∃∃T. L2 ⊢ T1 [d, e] ▶* T & L1 ⊢ T2 [ds, es] ▶* T.
/3 width=1/ qed.

(* Advanced forward lemmas **************************************************)

lemma ltpsss_fwd_tpss21: ∀e,K1,I,V1,L2. 0 < e → K1. ⓑ{I} V1 [0, e] ▶** L2 →
                         ∃∃K2,V2. K1 [0, e - 1] ▶** K2 &
                                  K1 ⊢ V1 [0, e - 1] ▶* V2 &
                                  L2 = K2. ⓑ{I} V2.
#e #K1 #I #V1 #L2 #He #H @(ltpsss_ind … H) -L2
[ /2 width=5/
| #L #L2 #_ #HL2 * #K #V #HK1 #HV1 #H destruct
  elim (ltpss_inv_tpss21 … HL2 ?) -HL2 // #K2 #V2 #HK2 #HV2 #H
  lapply (ltpss_tpss_trans_eq … HV2 … HK2) -HV2 #HV2
  lapply (ltpsss_tpss_trans_eq … HK1 … HV2) -HV2 /3 width=5/
]
qed-.

lemma ltpsss_fwd_tpss11: ∀d,e,I,K1,V1,L2. 0 < d → K1. ⓑ{I} V1 [d, e] ▶** L2 →
                         ∃∃K2,V2. K1 [d - 1, e] ▶** K2 &
                                  K1 ⊢ V1 [d - 1, e] ▶* V2 &
                                  L2 = K2. ⓑ{I} V2.
#d #e #K1 #I #V1 #L2 #Hd #H @(ltpsss_ind … H) -L2
[ /2 width=5/
| #L #L2 #_ #HL2 * #K #V #HK1 #HV1 #H destruct
  elim (ltpss_inv_tpss11 … HL2 ?) -HL2 // #K2 #V2 #HK2 #HV2 #H
  lapply (ltpss_tpss_trans_eq … HV2 … HK2) -HV2 #HV2
  lapply (ltpsss_tpss_trans_eq … HK1 … HV2) -HV2 /3 width=5/
]
qed-.

lemma ltpsss_fwd_tpss22: ∀I,L1,K2,V2,e. L1 [0, e] ▶** K2. ⓑ{I} V2 → 0 < e →
                         ∃∃K1,V1. K1 [0, e - 1] ▶** K2 &
                                  K1 ⊢ V1 [0, e - 1] ▶* V2 &
                                  L1 = K1. ⓑ{I} V1.
#I #L1 #K2 #V2 #e #H #He @(ltpsss_ind_dx … H) -L1
[ /2 width=5/
| #L1 #L #HL1 #_ * #K #V #HK2 #HV2 #H destruct
  elim (ltpss_inv_tpss22 … HL1 ?) -HL1 // #K1 #V1 #HK1 #HV1 #H destruct 
  lapply (tpss_trans_eq … HV1 HV2) -V #HV12
  lapply (ltpss_tpss_trans_eq … HV12 … HK1) -HV12 /3 width=5/
]
qed-.

lemma ltpsss_inv_tpss12: ∀I,L1,K2,V2,d,e. L1 [d, e] ▶** K2. ⓑ{I} V2 → 0 < d →
                         ∃∃K1,V1. K1 [d - 1, e] ▶** K2 &
                                  K1 ⊢ V1 [d - 1, e] ▶* V2 &
                                  L1 = K1. ⓑ{I} V1.
#I #L1 #K2 #V2 #d #e #H #Hd @(ltpsss_ind_dx … H) -L1
[ /2 width=5/
| #L1 #L #HL1 #_ * #K #V #HK2 #HV2 #H destruct
  elim (ltpss_inv_tpss12 … HL1 ?) -HL1 // #K1 #V1 #HK1 #HV1 #H destruct 
  lapply (tpss_trans_eq … HV1 HV2) -V #HV12
  lapply (ltpss_tpss_trans_eq … HV12 … HK1) -HV12 /3 width=5/
]
qed-.

(* Main properties **********************************************************)

theorem ltpsss_conf: ∀L0,L1,d1,e1. L0 [d1, e1] ▶** L1 →
                     ∀L2,d2,e2. L0 [d2, e2] ▶** L2 →
                     ∃∃L. L1 [d2, e2] ▶** L & L2 [d1, e1] ▶** L.
/3 width=3/ qed.

theorem ltpsss_trans_eq: ∀L1,L,L2,d,e.
                         L1 [d, e] ▶** L → L [d, e] ▶** L2 → L1 [d, e] ▶** L2. 
/2 width=3/ qed.

lemma ltpsss_tpss2: ∀L1,L2,I,V1,V2,e.
                    L1 [0, e] ▶** L2 → L2 ⊢ V1 [0, e] ▶* V2 →
                    L1. ⓑ{I} V1 [0, e + 1] ▶** L2. ⓑ{I} V2.
#L1 #L2 #I #V1 #V2 #e #HL12 #H @(tpss_ind … H) -V2
[ /2 width=1/
| #V #V2 #_ #HV2 #IHV @(ltpsss_trans_eq … IHV) /2 width=1/
]
qed.

lemma ltpsss_tpss2_lt: ∀L1,L2,I,V1,V2,e.
                       L1 [0, e - 1] ▶** L2 → L2 ⊢ V1 [0, e - 1] ▶* V2 →
                       0 < e → L1. ⓑ{I} V1 [0, e] ▶** L2. ⓑ{I} V2.
#L1 #L2 #I #V1 #V2 #e #HL12 #HV12 #He
>(plus_minus_m_m e 1) // /2 width=1/
qed.

lemma ltpsss_tpss1: ∀L1,L2,I,V1,V2,d,e.
                    L1 [d, e] ▶** L2 → L2 ⊢ V1 [d, e] ▶* V2 →
                    L1. ⓑ{I} V1 [d + 1, e] ▶** L2. ⓑ{I} V2.
#L1 #L2 #I #V1 #V2 #d #e #HL12 #H @(tpss_ind … H) -V2
[ /2 width=1/
| #V #V2 #_ #HV2 #IHV @(ltpsss_trans_eq … IHV) /2 width=1/
]
qed.

lemma ltpsss_tpss1_lt: ∀L1,L2,I,V1,V2,d,e.
                       L1 [d - 1, e] ▶** L2 → L2 ⊢ V1 [d - 1, e] ▶* V2 →
                       0 < d → L1. ⓑ{I} V1 [d, e] ▶** L2. ⓑ{I} V2.
#L1 #L2 #I #V1 #V2 #d #e #HL12 #HV12 #Hd
>(plus_minus_m_m d 1) // /2 width=1/
qed.
