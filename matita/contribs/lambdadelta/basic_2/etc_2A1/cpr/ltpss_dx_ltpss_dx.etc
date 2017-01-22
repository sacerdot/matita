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

lemma ltpss_dx_tpss_trans_eq: ∀L1,T2,U2,d,e. L1 ⊢ T2 ▶* [d, e] U2 →
                              ∀L0. L0 ▶* [d, e] L1 → L0 ⊢ T2 ▶* [d, e] U2.
#L1 #T2 @(f2_ind … fw … L1 T2) -L1 -T2 #n #IH #L1 *
[ #I #Hn #W2 #d #e #H #L0 #HL01 destruct
  elim (tpss_inv_atom1 … H) -H // *
  #K1 #V1 #V2 #i #Hdi #Hide #HLK1 #HV12 #HVW2 #H destruct
  lapply (ldrop_fwd_lw … HLK1) #H1 normalize in H1;
  elim (ltpss_dx_ldrop_trans_be … HL01 … HLK1 ? ?) -HL01 -HLK1 // /2 width=2/ #X #H #HLK0
  elim (ltpss_dx_inv_tpss22 … H ?) -H /2 width=1/ #K0 #V0 #HK01 #HV01 #H destruct
  lapply (tpss_fwd_tw … HV01) #H2
  lapply (transitive_le (♯{K1} + ♯{V0}) … H1) -H1 /2 width=1/ -H2 #H
  lapply (tpss_trans_eq … HV01 HV12) -V1 #HV02
  lapply (IH … HV02 … HK01) -IH -HV02 -HK01
  [ normalize /2 width=1/ | /2 width=6/ ]
| * [ #a ] #I #V2 #T2 #Hn #X #d #e #H #L0 #HL0 destruct
  [ elim (tpss_inv_bind1 … H) -H #W2 #U2 #HVW2 #HTU2 #H destruct
    lapply (tpss_lsubr_trans … HTU2 (L1. ⓑ{I} V2) ?) -HTU2 /2 width=1/ #HTU2
    lapply (IH … HVW2 … HL0) -HVW2 [ /2 width=2/ ] #HVW2
    lapply (IH … HTU2 (L0. ⓑ{I} V2) ?) -IH -HTU2 // /2 width=2/ -HL0 #HTU2
    lapply (tpss_lsubr_trans … HTU2 (L0. ⓑ{I} W2) ?) -HTU2 /2 width=1/
  | elim (tpss_inv_flat1 … H) -H #W2 #U2 #HVW2 #HTU2 #H destruct
    lapply (IH … HVW2 … HL0) -HVW2 //
    lapply (IH … HTU2 … HL0) -IH -HTU2 // -HL0 /2 width=1/
]
qed.

lemma ltpss_dx_tps_trans_eq: ∀L0,L1,T2,U2,d,e. L0 ▶* [d, e] L1 →
                             L1 ⊢ T2 ▶ [d, e] U2 → L0 ⊢ T2 ▶* [d, e] U2.
/3 width=3/ qed.

(* Main properties **********************************************************)

theorem ltpss_dx_conf: ∀L0,L1,d1,e1. L0 ▶* [d1, e1] L1 →
                       ∀L2,d2,e2. L0 ▶* [d2, e2] L2 →
                       ∃∃L. L1 ▶* [d2, e2] L & L2 ▶* [d1, e1] L.
#L0 @(f_ind … lw … L0) -L0 #n #IH *
[ #_ #L1 #d1 #e1 #H1 #L2 #d2 #e2 #H2 -n
  >(ltpss_dx_inv_atom1 … H1) -L1
  >(ltpss_dx_inv_atom1 … H2) -L2 /2 width=3/
| #K0 #I0 #V0 #Hn #L1 #d1 #e1 #H1 #L2 #d2 #e2 #H2 destruct
  elim (eq_or_gt d1) #Hd1 [ elim (eq_or_gt e1) #He1 ] destruct
  [ lapply (ltpss_dx_inv_refl_O2 … H1) -H1 #H1
  | elim (ltpss_dx_inv_tpss21 … H1 … He1) -H1 #K1 #V1 #HK01 #HV01 #H1
  | elim (ltpss_dx_inv_tpss11 … H1 … Hd1) -H1 #K1 #V1 #HK01 #HV01 #H1
  ] destruct
  elim (eq_or_gt d2) #Hd2 [1,3,5: elim (eq_or_gt e2) #He2 ] destruct
  [1,3,5: lapply (ltpss_dx_inv_refl_O2 … H2) -H2 #H2
  |2,4,6: elim (ltpss_dx_inv_tpss21 … H2 … He2) -H2 #K2 #V2 #HK02 #HV02 #H2
  |7,8,9: elim (ltpss_dx_inv_tpss11 … H2 … Hd2) -H2 #K2 #V2 #HK02 #HV02 #H2
  ] destruct
  [1: -IH /2 width=3/
  |2,3,4,7: -IH /3 width=5/
  |5,6,8,9:
    elim (IH … HK01 … HK02) // -K0 #K #HK1 #HK2
    elim (ltpss_dx_tpss_conf … HV01 … HK1) -HV01 #W1 #HW1 #HVW1
    elim (ltpss_dx_tpss_conf … HV02 … HK2) -HV02 #W2 #HW2 #HVW2
    elim (tpss_conf_eq … HW1 … HW2) -V0 #V #HW1 #HW2
    lapply (tpss_trans_eq … HVW1 HW1) -W1
    lapply (tpss_trans_eq … HVW2 HW2) -W2 /3 width=5/
  ]
]
qed.
