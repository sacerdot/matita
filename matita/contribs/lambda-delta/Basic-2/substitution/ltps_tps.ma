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

include "Basic-2/substitution/tps_lift.ma".
include "Basic-2/substitution/ltps_drop.ma".

(* PARALLEL SUBSTITUTION ON LOCAL ENVIRONMENTS ******************************)

lemma ltps_tps_conf_ge: ∀L0,T2,U2,d2,e2. L0 ⊢ T2 [d2, e2] ≫ U2 →
                        ∀L1,d1,e1. L0 [d1, e1] ≫ L1 → d1 + e1 ≤ d2 →
                        L1 ⊢ T2 [d2, e2] ≫ U2.
#L0 #T2 #U2 #d2 #e2 #H elim H -H L0 T2 U2 d2 e2
[ //
| #L0 #K0 #V0 #W0 #i2 #d2 #e2 #Hdi2 #Hide2 #HLK0 #HVW0 #L1 #d1 #e1 #HL01 #Hde1d2
  lapply (transitive_le … Hde1d2 Hdi2) -Hde1d2 #Hde1i2
  lapply (ltps_drop_conf_ge … HL01 … HLK0 ?) -HL01 HLK0 /2/
| #L0 #I #V2 #W2 #T2 #U2 #d2 #e2 #_ #_ #IHVW2 #IHTU2 #L1 #d1 #e1 #HL01 #Hde1d2
  @tps_bind [ /2/ | @IHTU2 [3: /2/ |1,2: skip | /2/ ] ] (**) (* /3/ is too slow *)
| /3/
]
qed.

lemma ltps_tps_conf: ∀L0,T2,U2,d2,e2. L0 ⊢ T2 [d2, e2] ≫ U2 →
                     ∀L1,d1,e1. L0 [d1, e1] ≫ L1 →
                     ∃∃T. L1 ⊢ T2 [d2, e2] ≫ T &
                          L1 ⊢ U2 [d1, e1] ≫ T.
#L0 #T2 #U2 #d2 #e2 #H elim H -H L0 T2 U2 d2 e2
[ /2/
| #L0 #K0 #V0 #W0 #i2 #d2 #e2 #Hdi2 #Hide2 #HLK0 #HVW0 #L1 #d1 #e1 #HL01
  elim (lt_or_ge i2 d1) #Hi2d1
  [ elim (ltps_drop_conf_le … HL01 … HLK0 ?) -HL01 HLK0 /2/ #X #H #HLK1
    elim (ltps_inv_tps11 … H ?) -H [2: /2/ ] #K1 #V1 #_ #HV01 #H destruct -X;
    lapply (drop_fwd_drop2 … HLK1) #H
    elim (lift_total V1 0 (i2 + 1)) #W1 #HVW1
    lapply (tps_lift_ge … HV01 … H HVW0 HVW1 ?) -H HV01 HVW0 // >arith_a2 /3/
  | elim (lt_or_ge i2 (d1 + e1)) #Hde1i2
    [ elim (ltps_drop_conf_be … HL01 … HLK0 ? ?) -HL01 HLK0 [2,3: /2/ ] #X #H #HLK1
      elim (ltps_inv_tps21 … H ?) -H [2: /2/ ] #K1 #V1 #_ #HV01 #H destruct -X;
      lapply (drop_fwd_drop2 … HLK1) #H
      elim (lift_total V1 0 (i2 + 1)) #W1 #HVW1
      lapply (tps_lift_ge … HV01 … H HVW0 HVW1 ?) -H HV01 HVW0 // normalize #HW01
      lapply (tps_weak … HW01 d1 e1 ? ?) [2,3: /3/ ] >arith_i2 //
    | lapply (ltps_drop_conf_ge … HL01 … HLK0 ?) -HL01 HLK0 /3/
    ]
  ]
| #L0 #I #V2 #W2 #T2 #U2 #d2 #e2 #_ #_ #IHVW2 #IHTU2 #L1 #d1 #e1 #HL01
  elim (IHVW2 … HL01) -IHVW2 #V #HV2 #HVW2
  elim (IHTU2 (L1. 𝕓{I} V) (d1 + 1) e1 ?) -IHTU2 [2: /2/ ] -HL01 /3 width=5/
| #L0 #I #V2 #W2 #T2 #U2 #d2 #e2 #_ #_ #IHVW2 #IHTU2 #L1 #d1 #e1 #HL01
  elim (IHVW2 … HL01) -IHVW2;
  elim (IHTU2 … HL01) -IHTU2 HL01 /3 width=5/
]
qed.

lemma ltps_tps_trans_ge: ∀L0,T2,U2,d2,e2. L0 ⊢ T2 [d2, e2] ≫ U2 →
                         ∀L1,d1,e1. L1 [d1, e1] ≫ L0 → d1 + e1 ≤ d2 →
                         L1 ⊢ T2 [d2, e2] ≫ U2.
#L0 #T2 #U2 #d2 #e2 #H elim H -H L0 T2 U2 d2 e2
[ //
| #L0 #K0 #V0 #W0 #i2 #d2 #e2 #Hdi2 #Hide2 #HLK0 #HVW0 #L1 #d1 #e1 #HL10 #Hde1d2
  lapply (transitive_le … Hde1d2 Hdi2) -Hde1d2 #Hde1i2
  lapply (ltps_drop_trans_ge … HL10 … HLK0 ?) -HL10 HLK0 /2/
| #L0 #I #V2 #W2 #T2 #U2 #d2 #e2 #_ #_ #IHVW2 #IHTU2 #L1 #d1 #e1 #HL10 #Hde1d2
  @tps_bind [ /2/ | @IHTU2 [3: /2/ |1,2: skip | /2/ ] ] (**) (* /3/ is too slow *)
| /3/
]
qed.

lemma ltps_tps_trans: ∀L0,T2,U2,d2,e2. L0 ⊢ T2 [d2, e2] ≫ U2 →
                      ∀L1,d1,e1. L1 [d1, e1] ≫ L0 →
                      ∃∃T. L1 ⊢ T2 [d2, e2] ≫ T &
                           L0 ⊢ T [d1, e1] ≫ U2.
#L0 #T2 #U2 #d2 #e2 #H elim H -H L0 T2 U2 d2 e2
[ /2/
| #L0 #K0 #V0 #W0 #i2 #d2 #e2 #Hdi2 #Hide2 #HLK0 #HVW0 #L1 #d1 #e1 #HL10
  elim (lt_or_ge i2 d1) #Hi2d1
  [ elim (ltps_drop_trans_le … HL10 … HLK0 ?) -HL10 /2/ #X #H #HLK1
    elim (ltps_inv_tps12 … H ?) -H [2: /2/ ] #K1 #V1 #_ #HV01 #H destruct -X;
    lapply (drop_fwd_drop2 … HLK0) -HLK0 #H
    elim (lift_total V1 0 (i2 + 1)) #W1 #HVW1
    lapply (tps_lift_ge … HV01 … H HVW1 HVW0 ?) -H HV01 HVW0 // >arith_a2 /3/
  | elim (lt_or_ge i2 (d1 + e1)) #Hde1i2
    [ elim (ltps_drop_trans_be … HL10 … HLK0 ? ?) -HL10 [2,3: /2/ ] #X #H #HLK1
      elim (ltps_inv_tps22 … H ?) -H [2: /2/ ] #K1 #V1 #_ #HV01 #H destruct -X;
      lapply (drop_fwd_drop2 … HLK0) -HLK0 #H
      elim (lift_total V1 0 (i2 + 1)) #W1 #HVW1
      lapply (tps_lift_ge … HV01 … H HVW1 HVW0 ?) -H HV01 HVW0 // normalize #HW01
      lapply (tps_weak … HW01 d1 e1 ? ?) [2,3: /3/ ] >arith_i2 //
    | lapply (ltps_drop_trans_ge … HL10 … HLK0 ?) -HL10 HLK0 /3/
    ]
  ]
| #L0 #I #V2 #W2 #T2 #U2 #d2 #e2 #_ #_ #IHVW2 #IHTU2 #L1 #d1 #e1 #HL10
  elim (IHVW2 … HL10) -IHVW2 #V #HV2 #HVW2
  elim (IHTU2 (L1. 𝕓{I} V) (d1 + 1) e1 ?) -IHTU2 [2: /2/ ] -HL10 /3 width=5/
| #L0 #I #V2 #W2 #T2 #U2 #d2 #e2 #_ #_ #IHVW2 #IHTU2 #L1 #d1 #e1 #HL10
  elim (IHVW2 … HL10) -IHVW2;
  elim (IHTU2 … HL10) -IHTU2 HL10 /3 width=5/
]
qed.
