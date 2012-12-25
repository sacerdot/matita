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
include "basic_2/unfold/tpss_alt.ma".
include "basic_2/unfold/ltpss_dx_tpss.ma".

(* DX PARTIAL UNFOLD ON LOCAL ENVIRONMENTS **********************************)

(* Advanced properties ******************************************************)

lemma ltpss_dx_tpss_conf: ∀L0,T2,U2,d2,e2. L0 ⊢ T2 ▶* [d2, e2] U2 →
                          ∀L1,d1,e1. L0 ▶* [d1, e1] L1 →
                          ∃∃T. L1 ⊢ T2 ▶* [d2, e2] T &
                               L1 ⊢ U2 ▶* [d1, e1] T.
#L0 #T2 #U2 #d2 #e2 #H #L1 #d1 #e1 #HL01 @(tpss_ind … H) -U2 /2 width=3/
#U #U2 #_ #HU2 * #X2 #HTX2 #HUX2
elim (ltpss_dx_tps_conf … HU2 … HL01) -L0 #X1 #HUX1 #HU2X1
elim (tpss_strip_eq … HUX2 … HUX1) -U #X #HX2 #HX1
lapply (tpss_trans_eq … HU2X1 … HX1) -X1 /3 width=3/
qed.

lemma ltpss_dx_tpss_trans_down: ∀L0,L1,T2,U2,d1,e1,d2,e2. d2 + e2 ≤ d1 →
                                L1 ▶* [d1, e1] L0 → L0 ⊢ T2 ▶* [d2, e2] U2 →
                                ∃∃T. L1 ⊢ T2 ▶* [d2, e2] T & L0 ⊢ T ▶* [d1, e1] U2.
#L0 #L1 #T2 #U2 #d1 #e1 #d2 #e2 #Hde2d1 #HL10 #H @(tpss_ind … H) -U2
[ /2 width=3/
| #U #U2 #_ #HU2 * #T #HT2 #HTU
  elim (tpss_strap1_down … HTU … HU2 ?) -U // #U #HTU #HU2
  elim (ltpss_dx_tps_trans … HTU … HL10) -HTU -HL10 #X #HTX #HXU
  lapply (tpss_trans_eq … HXU HU2) -U /3 width=3/
]
qed.

fact ltpss_dx_tpss_trans_eq_aux: ∀Y1,X2,L1,T2,U2,d,e.
                                 L1 ⊢ T2 ▶* [d, e] U2 → ∀L0. L0 ▶* [d, e] L1 →
                                 Y1 = L1 → X2 = T2 → L0 ⊢ T2 ▶* [d, e] U2.
#Y1 #X2 @(fw_ind … Y1 X2) -Y1 -X2 #Y1 #X2 #IH
#L1 #T2 #U2 #d #e #H @(tpss_ind_alt … H) -L1 -T2 -U2 -d -e
[ //
| #L1 #K1 #V1 #V2 #W2 #i #d #e #Hdi #Hide #HLK1 #HV12 #HVW2 #_ #L0 #HL01 #H1 #H2 destruct
  lapply (ldrop_fwd_lw … HLK1) #H1 normalize in H1;
  elim (ltpss_dx_ldrop_trans_be … HL01 … HLK1 ? ?) -HL01 -HLK1 // /2 width=2/ #X #H #HLK0
  elim (ltpss_dx_inv_tpss22 … H ?) -H /2 width=1/ #K0 #V0 #HK01 #HV01 #H destruct
  lapply (tpss_fwd_tw … HV01) #H2
  lapply (transitive_le (#{K1} + #{V0}) … H1) -H1 /2 width=1/ -H2 #H
  lapply (tpss_trans_eq … HV01 HV12) -V1 #HV02
  lapply (IH … HV02 … HK01 ? ?) -IH -HV02 -HK01
  [1,3: // |2,4: skip | normalize /2 width=1/ | /2 width=6/ ]
| #L #a #I #V1 #V2 #T1 #T2 #d #e #HV12 #HT12 #_ #_ #L0 #HL0 #H1 #H2 destruct
  lapply (tpss_lsubs_trans … HT12 (L. ⓑ{I} V1) ?) -HT12 /2 width=1/ #HT12
  lapply (IH … HV12 … HL0 ? ?) -HV12 [1,3: // |2,4: skip |5: /2 width=2/ ] #HV12
  lapply (IH … HT12 (L0. ⓑ{I} V1) ? ? ?) -IH -HT12 [1,3,5: /2 width=2/ |2,4: skip | normalize // ] -HL0 #HT12
  lapply (tpss_lsubs_trans … HT12 (L0. ⓑ{I} V2) ?) -HT12 /2 width=1/
| #L #I #V1 #V2 #T1 #T2 #d #e #HV12 #HT12 #_ #_ #L0 #HL0 #H1 #H2 destruct
  lapply (IH … HV12 … HL0 ? ?) -HV12 [1,3: // |2,4: skip |5: /2 width=3/ ]
  lapply (IH … HT12 … HL0 ? ?) -IH -HT12 [1,3,5: normalize // |2,4: skip ] -HL0 /2 width=1/
]
qed.

lemma ltpss_dx_tpss_trans_eq: ∀L1,T2,U2,d,e. L1 ⊢ T2 ▶* [d, e] U2 →
                              ∀L0. L0 ▶* [d, e] L1 → L0 ⊢ T2 ▶* [d, e] U2.
/2 width=5/ qed.

lemma ltpss_dx_tps_trans_eq: ∀L0,L1,T2,U2,d,e. L0 ▶* [d, e] L1 →
                             L1 ⊢ T2 ▶ [d, e] U2 → L0 ⊢ T2 ▶* [d, e] U2.
/3 width=3/ qed.

(* Main properties **********************************************************)

fact ltpss_dx_conf_aux: ∀K,K1,L1,d1,e1. K1 ▶* [d1, e1] L1 →
                        ∀K2,L2,d2,e2. K2 ▶* [d2, e2] L2 → K1 = K → K2 = K →
                        ∃∃L. L1 ▶* [d2, e2] L & L2 ▶* [d1, e1] L.
#K @(lw_ind … K) -K #K #IH #K1 #L1 #d1 #e1 * -K1 -L1 -d1 -e1
[ -IH /2 width=3/
| -IH #K1 #I1 #V1 #K2 #L2 #d2 #e2 * -K2 -L2 -d2 -e2
  [ /2 width=3/
  | #K2 #I2 #V2 #H1 #H2 destruct /2 width=3/
  | #K2 #L2 #I2 #W2 #V2 #e2 #HKL2 #HWV2 #H1 #H2 destruct /3 width=3/
  | #K2 #L2 #I2 #W2 #V2 #d2 #e2 #HKL2 #HWV2 #H1 #H2 destruct /3 width=3/
  ]
| #K1 #L1 #I1 #W1 #V1 #e1 #HKL1 #HWV1 #K2 #L2 #d2 #e2 * -K2 -L2 -d2 -e2
  [ -IH #d2 #e2 #H1 #H2 destruct
  | -IH #K2 #I2 #V2 #H1 #H2 destruct /3 width=5/
  | #K2 #L2 #I2 #W2 #V2 #e2 #HKL2 #HWV2 #H1 #H2 destruct
    elim (IH … HKL1 … HKL2 ? ?) -IH [2,4: // |3: skip |5: /2 width=1/ ] -K1 #L #HL1 #HL2
    elim (ltpss_dx_tpss_conf … HWV1 … HL1) #U1 #HWU1 #HVU1
    elim (ltpss_dx_tpss_conf … HWV2 … HL2) #U2 #HWU2 #HVU2
    elim (tpss_conf_eq … HWU1 … HWU2) -W1 #W #HU1W #HU2W
    lapply (tpss_trans_eq … HVU1 HU1W) -U1
    lapply (tpss_trans_eq … HVU2 HU2W) -U2 /3 width=5/
  | #K2 #L2 #I2 #W2 #V2 #d2 #e2 #HKL2 #HWV2 #H1 #H2 destruct
    elim (IH … HKL1 … HKL2 ? ?) -IH [2,4: // |3: skip |5: /2 width=1/ ] -K1 #L #HL1 #HL2
    elim (ltpss_dx_tpss_conf … HWV1 … HL1) #U1 #HWU1 #HVU1
    elim (ltpss_dx_tpss_conf … HWV2 … HL2) #U2 #HWU2 #HVU2
    elim (tpss_conf_eq … HWU1 … HWU2) -W1 #W #HU1W #HU2W
    lapply (tpss_trans_eq … HVU1 HU1W) -U1
    lapply (tpss_trans_eq … HVU2 HU2W) -U2 /3 width=5/
  ]
| #K1 #L1 #I1 #W1 #V1 #d1 #e1 #HKL1 #HWV1 #K2 #L2 #d2 #e2 * -K2 -L2 -d2 -e2
  [ -IH #d2 #e2 #H1 #H2 destruct
  | -IH #K2 #I2 #V2 #H1 #H2 destruct /3 width=5/
  | #K2 #L2 #I2 #W2 #V2 #e2 #HKL2 #HWV2 #H1 #H2 destruct
    elim (IH … HKL1 … HKL2 ? ?) -IH [2,4: // |3: skip |5: /2 width=1/ ] -K1 #L #HL1 #HL2
    elim (ltpss_dx_tpss_conf … HWV1 … HL1) #U1 #HWU1 #HVU1
    elim (ltpss_dx_tpss_conf … HWV2 … HL2) #U2 #HWU2 #HVU2
    elim (tpss_conf_eq … HWU1 … HWU2) -W1 #W #HU1W #HU2W
    lapply (tpss_trans_eq … HVU1 HU1W) -U1
    lapply (tpss_trans_eq … HVU2 HU2W) -U2 /3 width=5/
  | #K2 #L2 #I2 #W2 #V2 #d2 #e2 #HKL2 #HWV2 #H1 #H2 destruct
    elim (IH … HKL1 … HKL2 ? ?) -IH [2,4: // |3: skip |5: /2 width=1/ ] -K1 #L #HL1 #HL2
    elim (ltpss_dx_tpss_conf … HWV1 … HL1) #U1 #HWU1 #HVU1
    elim (ltpss_dx_tpss_conf … HWV2 … HL2) #U2 #HWU2 #HVU2
    elim (tpss_conf_eq … HWU1 … HWU2) -W1 #W #HU1W #HU2W
    lapply (tpss_trans_eq … HVU1 HU1W) -U1
    lapply (tpss_trans_eq … HVU2 HU2W) -U2 /3 width=5/
  ]
]
qed.

theorem ltpss_dx_conf: ∀L0,L1,d1,e1. L0 ▶* [d1, e1] L1 →
                       ∀L2,d2,e2. L0 ▶* [d2, e2] L2 →
                       ∃∃L. L1 ▶* [d2, e2] L & L2 ▶* [d1, e1] L.
/2 width=7/ qed.
