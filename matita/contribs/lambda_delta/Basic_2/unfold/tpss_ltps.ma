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

include "Basic_2/substitution/ltps_tps.ma".
include "Basic_2/unfold/tpss_tpss.ma".

(* PARTIAL UNFOLD ON TERMS **************************************************)

(* Properties concerning parallel substitution on local environments ********)

lemma ltps_tpss_conf_ge: ∀L0,L1,T2,U2,d1,e1,d2,e2.
                         d1 + e1 ≤ d2 → L0 [d1, e1] ≫ L1 →
                         L0 ⊢ T2 [d2, e2] ≫* U2 → L1 ⊢ T2 [d2, e2] ≫* U2.
#L0 #L1 #T2 #U2 #d1 #e1 #d2 #e2 #Hde1d2 #HL01 #H @(tpss_ind … H) -U2 //
#U #U2 #_ #HU2 #IHU
lapply (ltps_tps_conf_ge … HU2 … HL01 ?) -HU2 -HL01 // /2 width=3/
qed.

lemma ltps_tpss_conf: ∀L0,L1,T2,U2,d1,e1,d2,e2.
                      L0 [d1, e1] ≫ L1 → L0 ⊢ T2 [d2, e2] ≫* U2 →
                      ∃∃T. L1 ⊢ T2 [d2, e2] ≫* T & L1 ⊢ U2 [d1, e1] ≫* T.
#L0 #L1 #T2 #U2 #d1 #e1 #d2 #e2 #HL01 #H @(tpss_ind … H) -U2
[ /3 width=3/
| #U #U2 #_ #HU2 * #T #HT2 #HUT
  elim (ltps_tps_conf … HU2 … HL01) -HU2 -HL01 #W #HUW #HU2W
  elim (tpss_strip_eq … HUT … HUW) -U
  /3 width=5 by ex2_1_intro, step, tpss_strap/ (**) (* just /3 width=5/ is too slow *)
]
qed.

lemma ltps_tpss_trans_ge: ∀L0,L1,T2,U2,d1,e1,d2,e2.
                          d1 + e1 ≤ d2 → L1 [d1, e1] ≫ L0 →
                          L0 ⊢ T2 [d2, e2] ≫* U2 → L1 ⊢ T2 [d2, e2] ≫* U2.
#L0 #L1 #T2 #U2 #d1 #e1 #d2 #e2 #Hde1d2 #HL10 #H @(tpss_ind … H) -U2 //
#U #U2 #_ #HU2 #IHU
lapply (ltps_tps_trans_ge … HU2 … HL10 ?) -HU2 -HL10 // /2 width=3/
qed.

lemma ltps_tpss_trans_down: ∀L0,L1,T2,U2,d1,e1,d2,e2. d2 + e2 ≤ d1 →
                            L1 [d1, e1] ≫ L0 → L0 ⊢ T2 [d2, e2] ≫* U2 →
                            ∃∃T. L1 ⊢ T2 [d2, e2] ≫* T & L0 ⊢ T [d1, e1] ≫* U2.
#L0 #L1 #T2 #U2 #d1 #e1 #d2 #e2 #Hde2d1 #HL10 #H @(tpss_ind … H) -U2
[ /3 width=3/
| #U #U2 #_ #HU2 * #T #HT2 #HTU
  elim (tpss_strap1_down … HTU … HU2 ?) -U // #U #HTU #HU2
  elim (ltps_tps_trans … HTU … HL10) -HTU -HL10 #W #HTW #HWU
  @(ex2_1_intro … W) /2 width=3/ (**) (* /3 width=5/ does not work as in ltps_tpss_conf *)
]
qed.

fact ltps_tps_trans_eq_aux: ∀Y1,X2,L1,T2,U2,d,e.
                            L1 ⊢ T2 [d, e] ≫ U2 → ∀L0. L0 [d, e] ≫ L1 →
                            Y1 = L1 → X2 = T2 → L0 ⊢ T2 [d, e] ≫* U2.
#Y1 #X2 @(cw_wf_ind … Y1 X2) -Y1 -X2 #Y1 #X2 #IH
#L1 #T2 #U2 #d #e * -L1 -T2 -U2 -d -e
[ //
| #L1 #K1 #V1 #W1 #i #d #e #Hdi #Hide #HLK1 #HVW1 #L0 #HL10 #H1 #H2 destruct
  lapply (ldrop_fwd_lw … HLK1) normalize #H1
  elim (ltps_ldrop_trans_be … HL10 … HLK1 ? ?) -HL10 -HLK1 /2 width=1/ #X #H #HLK0
  elim (ltps_inv_tps22 … H ?) -H /2 width=1/ #K0 #V0 #HK01 #HV01 #H destruct
  lapply (tps_fwd_tw … HV01) #H2
  lapply (transitive_le (#[K1] + #[V0]) … H1) -H1 /2 width=1/ -H2 #H
  lapply (IH … HV01 … HK01 ? ?) -IH -HV01 -HK01
  [1,3: // |2,4: skip | normalize /2 width=1/ | /3 width=6/ ]
| #L #I #V1 #V2 #T1 #T2 #d #e #HV12 #HT12 #L0 #HL0 #H1 #H2 destruct
  lapply (tps_lsubs_conf … HT12 (L. 𝕓{I} V1) ?) -HT12 /2 width=1/ #HT12
  lapply (IH … HV12 … HL0 ? ?) -HV12 [1,3,5: normalize // |2,4: skip ] #HV12
  lapply (IH … HT12 (L0. 𝕓{I} V1) ? ? ?) -IH -HT12 [1,3,5: /2 width=2/ |2,4: skip | normalize // ] -HL0 #HT12
  lapply (tpss_lsubs_conf … HT12 (L0. 𝕓{I} V2) ?) -HT12 /2 width=1/
| #L #I #V1 #V2 #T1 #T2 #d #e #HV12 #HT12 #L0 #HL0 #H1 #H2 destruct
  lapply (IH … HV12 … HL0 ? ?) -HV12 [1,3,5: normalize // |2,4: skip ]
  lapply (IH … HT12 … HL0 ? ?) -IH -HT12 [1,3,5: normalize // |2,4: skip ] -HL0 /2 width=1/
]
qed.

lemma ltps_tps_trans_eq: ∀L1,T2,U2,d,e. L1 ⊢ T2 [d, e] ≫ U2 →
                         ∀L0. L0 [d, e] ≫ L1 → L0 ⊢ T2 [d, e] ≫* U2.
/2 width=5/ qed.

lemma ltps_tpss_trans_eq: ∀L0,L1,T2,U2,d,e. L0 [d, e] ≫ L1 →
                          L1 ⊢ T2 [d, e] ≫* U2 → L0 ⊢ T2 [d, e] ≫* U2.
#L0 #L1 #T2 #U2 #d #e #HL01 #H @(tpss_ind … H) -U2 //
#U #U2 #_ #HU2 #IHU @(tpss_trans_eq … IHU) /2 width=3/
qed.
