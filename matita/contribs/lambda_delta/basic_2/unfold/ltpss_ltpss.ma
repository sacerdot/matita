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

lemma ltpss_tpss_conf: ∀L0,T2,U2,d2,e2. L0 ⊢ T2 [d2, e2] ▶* U2 →
                       ∀L1,d1,e1. L0 [d1, e1] ▶* L1 →
                       ∃∃T. L1 ⊢ T2 [d2, e2] ▶* T &
                            L1 ⊢ U2 [d1, e1] ▶* T.
#L0 #T2 #U2 #d2 #e2 #H #L1 #d1 #e1 #HL01 @(tpss_ind … H) -U2 /2 width=3/
#U #U2 #_ #HU2 * #X2 #HTX2 #HUX2
elim (ltpss_tps_conf … HU2 … HL01) -L0 #X1 #HUX1 #HU2X1
elim (tpss_strip_eq … HUX2 … HUX1) -U #X #HX2 #HX1
lapply (tpss_trans_eq … HU2X1 … HX1) -X1 /3 width=3/
qed.

lemma ltpss_tpss_trans_down: ∀L0,L1,T2,U2,d1,e1,d2,e2. d2 + e2 ≤ d1 →
                             L1 [d1, e1] ▶* L0 → L0 ⊢ T2 [d2, e2] ▶* U2 →
                             ∃∃T. L1 ⊢ T2 [d2, e2] ▶* T & L0 ⊢ T [d1, e1] ▶* U2.
#L0 #L1 #T2 #U2 #d1 #e1 #d2 #e2 #Hde2d1 #HL10 #H @(tpss_ind … H) -U2
[ /2 width=3/
| #U #U2 #_ #HU2 * #T #HT2 #HTU
  elim (tpss_strap1_down … HTU … HU2 ?) -U // #U #HTU #HU2
  elim (ltpss_tps_trans … HTU … HL10) -HTU -HL10 #X #HTX #HXU
  lapply (tpss_trans_eq … HXU HU2) -U /3 width=3/
]
qed.

(* Main properties **********************************************************)

fact ltpss_conf_aux: ∀K,K1,L1,d1,e1. K1 [d1, e1] ▶* L1 →
                     ∀K2,L2,d2,e2. K2 [d2, e2] ▶* L2 → K1 = K → K2 = K →
                     ∃∃L. L1 [d2, e2] ▶* L & L2 [d1, e1] ▶* L.
#K @(lw_wf_ind … K) -K #K #IH #K1 #L1 #d1 #e1 * -K1 -L1 -d1 -e1
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
    elim (ltpss_tpss_conf … HWV1 … HL1) #U1 #HWU1 #HVU1
    elim (ltpss_tpss_conf … HWV2 … HL2) #U2 #HWU2 #HVU2
    elim (tpss_conf_eq … HWU1 … HWU2) -W1 #W #HU1W #HU2W
    lapply (tpss_trans_eq … HVU1 HU1W) -U1
    lapply (tpss_trans_eq … HVU2 HU2W) -U2 /3 width=5/
  | #K2 #L2 #I2 #W2 #V2 #d2 #e2 #HKL2 #HWV2 #H1 #H2 destruct
    elim (IH … HKL1 … HKL2 ? ?) -IH [2,4: // |3: skip |5: /2 width=1/ ] -K1 #L #HL1 #HL2
    elim (ltpss_tpss_conf … HWV1 … HL1) #U1 #HWU1 #HVU1
    elim (ltpss_tpss_conf … HWV2 … HL2) #U2 #HWU2 #HVU2
    elim (tpss_conf_eq … HWU1 … HWU2) -W1 #W #HU1W #HU2W
    lapply (tpss_trans_eq … HVU1 HU1W) -U1
    lapply (tpss_trans_eq … HVU2 HU2W) -U2 /3 width=5/
  ]
| #K1 #L1 #I1 #W1 #V1 #d1 #e1 #HKL1 #HWV1 #K2 #L2 #d2 #e2 * -K2 -L2 -d2 -e2
  [ -IH #d2 #e2 #H1 #H2 destruct
  | -IH #K2 #I2 #V2 #H1 #H2 destruct /3 width=5/
  | #K2 #L2 #I2 #W2 #V2 #e2 #HKL2 #HWV2 #H1 #H2 destruct
    elim (IH … HKL1 … HKL2 ? ?) -IH [2,4: // |3: skip |5: /2 width=1/ ] -K1 #L #HL1 #HL2
    elim (ltpss_tpss_conf … HWV1 … HL1) #U1 #HWU1 #HVU1
    elim (ltpss_tpss_conf … HWV2 … HL2) #U2 #HWU2 #HVU2
    elim (tpss_conf_eq … HWU1 … HWU2) -W1 #W #HU1W #HU2W
    lapply (tpss_trans_eq … HVU1 HU1W) -U1
    lapply (tpss_trans_eq … HVU2 HU2W) -U2 /3 width=5/
  | #K2 #L2 #I2 #W2 #V2 #d2 #e2 #HKL2 #HWV2 #H1 #H2 destruct
    elim (IH … HKL1 … HKL2 ? ?) -IH [2,4: // |3: skip |5: /2 width=1/ ] -K1 #L #HL1 #HL2
    elim (ltpss_tpss_conf … HWV1 … HL1) #U1 #HWU1 #HVU1
    elim (ltpss_tpss_conf … HWV2 … HL2) #U2 #HWU2 #HVU2
    elim (tpss_conf_eq … HWU1 … HWU2) -W1 #W #HU1W #HU2W
    lapply (tpss_trans_eq … HVU1 HU1W) -U1
    lapply (tpss_trans_eq … HVU2 HU2W) -U2 /3 width=5/
  ]
]
qed.

lemma ltpss_conf: ∀L0,L1,d1,e1. L0 [d1, e1] ▶* L1 →
                  ∀L2,d2,e2. L0 [d2, e2] ▶* L2 →
                  ∃∃L. L1 [d2, e2] ▶* L & L2 [d1, e1] ▶* L.
/2 width=7/ qed.
