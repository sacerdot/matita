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

include "basic_2/unfold/ltpss_sn_ldrop.ma".

(* SN PARALLEL UNFOLD ON LOCAL ENVIRONMENTS *********************************)

(* Properties concerning partial substitution on terms **********************)

lemma ltpss_sn_tps_conf_ge: ∀L0,T2,U2,d2,e2. L0 ⊢ T2 ▶ [d2, e2] U2 →
                            ∀L1,d1,e1. L0 ⊢ ▶* [d1, e1] L1 → d1 + e1 ≤ d2 →
                            L1 ⊢ T2 ▶ [d2, e2] U2.
#L0 #T2 #U2 #d2 #e2 #H elim H -L0 -T2 -U2 -d2 -e2
[ //
| #L0 #K0 #V0 #W0 #i2 #d2 #e2 #Hdi2 #Hide2 #HLK0 #HVW0 #L1 #d1 #e1 #HL01 #Hde1d2
  lapply (transitive_le … Hde1d2 Hdi2) -Hde1d2 #Hde1i2
  lapply (ltpss_sn_ldrop_conf_ge … HL01 … HLK0 ?) -L0 // /2 width=4/
| #L0 #a #I #V2 #W2 #T2 #U2 #d2 #e2 #_ #_ #IHVW2 #IHTU2 #L1 #d1 #e1 #HL01 #Hde1d2
  @tps_bind [ /2 width=4/ | @IHTU2 -IHTU2 -IHVW2 [3: /2 by ltpss_sn_tpss1/ |1,2: skip | /2 width=1/ ] ] (**) (* explicit constructor *)
| /3 width=4/
]
qed.

lemma ltpss_sn_tps_trans_ge: ∀L0,T2,U2,d2,e2. L0 ⊢ T2 ▶ [d2, e2] U2 →
                             ∀L1,d1,e1. L1 ⊢ ▶* [d1, e1] L0 → d1 + e1 ≤ d2 →
                             L1 ⊢ T2 ▶ [d2, e2] U2.
#L0 #T2 #U2 #d2 #e2 #H elim H -L0 -T2 -U2 -d2 -e2
[ //
| #L0 #K0 #V0 #W0 #i2 #d2 #e2 #Hdi2 #Hide2 #HLK0 #HVW0 #L1 #d1 #e1 #HL10 #Hde1d2
  lapply (transitive_le … Hde1d2 Hdi2) -Hde1d2 #Hde1i2
  lapply (ltpss_sn_ldrop_trans_ge … HL10 … HLK0 ?) -L0 // /2 width=4/
| #L0 #a #I #V2 #W2 #T2 #U2 #d2 #e2 #_ #_ #IHVW2 #IHTU2 #L1 #d1 #e1 #HL10 #Hde1d2
  @tps_bind [ /2 width=4/ | @IHTU2 -IHTU2 -IHVW2 [3: /2 by ltpss_sn_tpss1/ |1,2: skip | /2 width=1/ ] ] (**) (* explicit constructor *)
| /3 width=4/
]
qed.
