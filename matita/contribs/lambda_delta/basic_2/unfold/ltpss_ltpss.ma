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

include "basic_2/unfold/tpss_tpss.ma".
include "basic_2/unfold/ltpss_tpss.ma".

(* PARTIAL UNFOLD ON LOCAL ENVIRONMENTS *************************************)

(* Advanced properties ******************************************************)

(* Main properties **********************************************************)

theorem ltpss_trans_eq: ∀L1,L,L2,d,e.
                        L1 [d, e] ▶* L → L [d, e] ▶* L2 → L1 [d, e] ▶* L2. 
/2 width=3/ qed.

lemma ltpss_tpss2: ∀L1,L2,I,V1,V2,e.
                   L1 [0, e] ▶* L2 → L2 ⊢ V1 [0, e] ▶* V2 →
                   L1. ⓑ{I} V1 [0, e + 1] ▶* L2. ⓑ{I} V2.
#L1 #L2 #I #V1 #V2 #e #HL12 #H @(tpss_ind … H) -V2
[ /2 width=1/
| #V #V2 #_ #HV2 #IHV @(ltpss_trans_eq … IHV) /2 width=1/
]
qed.

lemma ltpss_tpss2_lt: ∀L1,L2,I,V1,V2,e.
                      L1 [0, e - 1] ▶* L2 → L2 ⊢ V1 [0, e - 1] ▶* V2 →
                      0 < e → L1. ⓑ{I} V1 [0, e] ▶* L2. ⓑ{I} V2.
#L1 #L2 #I #V1 #V2 #e #HL12 #HV12 #He
>(plus_minus_m_m e 1) // /2 width=1/
qed.

lemma ltpss_tpss1: ∀L1,L2,I,V1,V2,d,e.
                   L1 [d, e] ▶* L2 → L2 ⊢ V1 [d, e] ▶* V2 →
                   L1. ⓑ{I} V1 [d + 1, e] ▶* L2. ⓑ{I} V2.
#L1 #L2 #I #V1 #V2 #d #e #HL12 #H @(tpss_ind … H) -V2
[ /2 width=1/
| #V #V2 #_ #HV2 #IHV @(ltpss_trans_eq … IHV) /2 width=1/
]
qed.

lemma ltpss_tpss1_lt: ∀L1,L2,I,V1,V2,d,e.
                      L1 [d - 1, e] ▶* L2 → L2 ⊢ V1 [d - 1, e] ▶* V2 →
                      0 < d → L1. ⓑ{I} V1 [d, e] ▶* L2. ⓑ{I} V2.
#L1 #L2 #I #V1 #V2 #d #e #HL12 #HV12 #Hd
>(plus_minus_m_m d 1) // /2 width=1/
qed.

fact ltps_conf_aux: ∀K,K1,L1,d1,e1. K1 [d1, e1] ▶ L1 →
                    ∀K2,L2,d2,e2. K2 [d2, e2] ▶ L2 → K1 = K → K2 = K →
                    ∃∃L. L1 [d2, e2] ▶* L & L2 [d1, e1] ▶* L.
#K @(lw_wf_ind … K) -K #K #IH #K1 #L1 #d1 #e1 * -K1 -L1 -d1 -e1
[ -IH /3 width=3/
| -IH #K1 #I1 #V1 #K2 #L2 #d2 #e2 * -K2 -L2 -d2 -e2
  [ /2 width=3/
  | #K2 #I2 #V2 #H1 #H2 destruct /2 width=3/
  | #K2 #L2 #I2 #W2 #V2 #e2 #HKL2 #HWV2 #H1 #H2 destruct /4 width=3/
  | #K2 #L2 #I2 #W2 #V2 #d2 #e2 #HKL2 #HWV2 #H1 #H2 destruct /4 width=3/
  ]
| #K1 #L1 #I1 #W1 #V1 #e1 #HKL1 #HWV1 #K2 #L2 #d2 #e2 * -K2 -L2 -d2 -e2
  [ -IH #d2 #e2 #H1 #H2 destruct
  | -IH #K2 #I2 #V2 #H1 #H2 destruct
    @ex2_1_intro [2,3: @inj ] /3 width=5/ (**) (* /4 width=5/ is too slow *)
  | #K2 #L2 #I2 #W2 #V2 #e2 #HKL2 #HWV2 #H1 #H2 destruct
    elim (IH … HKL1 … HKL2 ? ?) -IH [2,4: // |3: skip |5: /2 width=1/ ] -K1 #L #HL1 #HL2
    elim (ltpss_tps_conf … HWV1 … HL1) #U1 #HWU1 #HVU1
    elim (ltpss_tps_conf … HWV2 … HL2) #U2 #HWU2 #HVU2
    elim (tpss_conf_eq … HWU1 … HWU2) -W1 #W #HU1W #HU2W
    @(ex2_1_intro … (L.ⓑ{I1}W)) (**) (* explicit constructor *)
    [ @(ltpss_trans_eq … (L1.ⓑ{I1}U1)) /2 width=1/
    | @(ltpss_trans_eq … (L2.ⓑ{I1}U2)) /2 width=1/
    ]
  | #K2 #L2 #I2 #W2 #V2 #d2 #e2 #HKL2 #HWV2 #H1 #H2 destruct
    elim (IH … HKL1 … HKL2 ? ?) -IH [2,4: // |3: skip |5: /2 width=1/ ] -K1 #L #HL1 #HL2
    elim (ltpss_tps_conf … HWV1 … HL1) #U1 #HWU1 #HVU1
    elim (ltpss_tps_conf … HWV2 … HL2) #U2 #HWU2 #HVU2
    elim (tpss_conf_eq … HWU1 … HWU2) -W1 #W #HU1W #HU2W
    @(ex2_1_intro … (L.ⓑ{I1}W)) (**) (* explicit constructor *)
    [ @(ltpss_trans_eq … (L1.ⓑ{I1}U1)) /2 width=1/
    | @(ltpss_trans_eq … (L2.ⓑ{I1}U2)) /2 width=1/
    ]
  ]
| #K1 #L1 #I1 #W1 #V1 #d1 #e1 #HKL1 #HWV1 #K2 #L2 #d2 #e2 * -K2 -L2 -d2 -e2
  [ -IH #d2 #e2 #H1 #H2 destruct
  | -IH #K2 #I2 #V2 #H1 #H2 destruct
    @ex2_1_intro [2,3: @inj ] /3 width=5/ (**) (* /4 width=5/ is too slow *)
  | #K2 #L2 #I2 #W2 #V2 #e2 #HKL2 #HWV2 #H1 #H2 destruct
    elim (IH … HKL1 … HKL2 ? ?) -IH [2,4: // |3: skip |5: /2 width=1/ ] -K1 #L #HL1 #HL2
    elim (ltpss_tps_conf … HWV1 … HL1) #U1 #HWU1 #HVU1
    elim (ltpss_tps_conf … HWV2 … HL2) #U2 #HWU2 #HVU2
    elim (tpss_conf_eq … HWU1 … HWU2) -W1 #W #HU1W #HU2W
    @(ex2_1_intro … (L.ⓑ{I1}W)) (**) (* explicit constructor *)
    [ @(ltpss_trans_eq … (L1.ⓑ{I1}U1)) /2 width=1/
    | @(ltpss_trans_eq … (L2.ⓑ{I1}U2)) /2 width=1/
    ]
  | #K2 #L2 #I2 #W2 #V2 #d2 #e2 #HKL2 #HWV2 #H1 #H2 destruct
    elim (IH … HKL1 … HKL2 ? ?) -IH [2,4: // |3: skip |5: /2 width=1/ ] -K1 #L #HL1 #HL2
    elim (ltpss_tps_conf … HWV1 … HL1) #U1 #HWU1 #HVU1
    elim (ltpss_tps_conf … HWV2 … HL2) #U2 #HWU2 #HVU2
    elim (tpss_conf_eq … HWU1 … HWU2) -W1 #W #HU1W #HU2W
    @(ex2_1_intro … (L.ⓑ{I1}W)) (**) (* explicit constructor *)
    [ @(ltpss_trans_eq … (L1.ⓑ{I1}U1)) /2 width=1/
    | @(ltpss_trans_eq … (L2.ⓑ{I1}U2)) /2 width=1/
    ]
  ]
]
qed.

lemma ltps_conf: ∀L0,L1,d1,e1. L0 [d1, e1] ▶ L1 →
                 ∀L2,d2,e2. L0 [d2, e2] ▶ L2 →
                 ∃∃L. L1 [d2, e2] ▶* L & L2 [d1, e1] ▶* L.
/2 width=7/ qed.

axiom ltpss_conf: ∀L0,L1,d1,e1. L0 [d1, e1] ▶* L1 →
                  ∀L2,d2,e2. L0 [d2, e2] ▶* L2 →
                  ∃∃L. L1 [d2, e2] ▶* L & L2 [d1, e1] ▶* L.
(*
fact ltpss_conf_aux: ∀K1,L1,d1,e1. K1 [d1, e1] ▶* L1 →
                     ∀K2,L2,d2,e2. K2 [d2, e2] ▶* L2 → K1 = K2 →
                     ∃∃L. L1 [d2, e2] ▶* L & L2 [d1, e1] ▶* L.
#K1 #L1 #d1 #e1 #H @(ltpss_ind_dx … H) -K1 /2 width=3/
#X1 #K1 #HXK1 #HKL1 #IHKL1 #K2 #L2 #d2 #e2 #H @(ltpss_ind_dx … H) -K2
[ -IHKL1 #H destruct
  lapply (ltpss_strap … HXK1 HKL1) -K1 /2 width=3/
| #X2 #K2 #HXK2 #HKL2 #_ #H destruct
  elim (ltps_conf … HXK1 … HXK2) -X2 #K #HK1 #HK2
  elim (IHKL1 … HK1 ?) // -K1 #L #HL1 #HKL
  @(ex2_1_intro … K) //
*)