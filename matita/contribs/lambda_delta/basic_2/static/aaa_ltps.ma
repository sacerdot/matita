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

include "basic_2/substitution/ltps_ldrop.ma".
include "basic_2/static/aaa_lift.ma".

(* ATONIC ARITY ASSIGNMENT ON TERMS *****************************************)

(* Properties about parallel substitution ***********************************)

(* Note: lemma 500 *)
lemma aaa_ltps_tps_conf: ∀L1,T1,A. L1 ⊢ T1 ÷ A → ∀L2,d,e. L1 [d, e] ▶ L2 →
                         ∀T2. L2 ⊢ T1 [d, e] ▶ T2 → L2 ⊢ T2 ÷ A.
#L1 #T1 #A #H elim H -L1 -T1 -A
[ #L1 #k #L2 #d #e #_ #T2 #H
  >(tps_inv_sort1 … H) -H //
| #I #L1 #K1 #V1 #B #i #HLK1 #_ #IHV1 #L2 #d #e #HL12 #T2 #H
  elim (tps_inv_lref1 … H) -H
  [ #H destruct
    elim (lt_or_ge i d) #Hdi
    [ elim (ltps_ldrop_conf_le … HL12 … HLK1 ?) -L1 /2 width=2/ #X #H #HLK2
      elim (ltps_inv_tps11 … H ?) -H /2 width=1/ -Hdi #K2 #V2 #HK12 #HV12 #H destruct
      /3 width=8/
    | elim (lt_or_ge i (d + e)) #Hide
      [ elim (ltps_ldrop_conf_be … HL12 … HLK1 ? ?) -L1 // /2 width=2/ #X #H #HLK2
        elim (ltps_inv_tps21 … H ?) -H /2 width=1/ -Hdi -Hide #K2 #V2 #HK12 #HV12 #H destruct
        /3 width=8/
      | -Hdi
        lapply (ltps_ldrop_conf_ge … HL12 … HLK1 ?) -L1 // -Hide #HLK2
        /3 width=8/
      ]
    ]
  | * #K2 #V2 #Hdi #Hide #HLK2 #HVT2
    elim (ltps_ldrop_conf_be … HL12 … HLK1 ? ?) -L1 // /2 width=2/ #X #H #HL2K0
    elim (ltps_inv_tps21 … H ?) -H /2 width=1/ -Hdi -Hide #K0 #V0 #HK12 #HV12 #H destruct
    lapply (ldrop_mono … HL2K0 … HLK2) -HL2K0 #H destruct
    lapply (ldrop_fwd_ldrop2 … HLK2) -HLK2 /3 width=7/
  ]
| #L1 #V1 #T1 #B #A #_ #_ #IHV1 #IHT1 #L2 #d #e #HL12 #X #H
  elim (tps_inv_bind1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct /4 width=4/
| #L1 #V1 #T1 #B #A #_ #_ #IHV1 #IHT1 #L2 #d #e #HL12 #X #H
  elim (tps_inv_bind1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct /4 width=4/
| #L1 #V1 #T1 #B #A #_ #_ #IHV1 #IHT1 #L2 #d #e #HL12 #X #H
  elim (tps_inv_flat1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct /3 width=4/
| #L1 #V1 #T1 #A #_ #_ #IHV1 #IHT1 #L2 #d #e #HL12 #X #H
  elim (tps_inv_flat1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct /3 width=4/
]
qed.

lemma aaa_ltps_conf: ∀L1,T,A. L1 ⊢ T ÷ A → ∀L2,d,e. L1 [d, e] ▶ L2 → L2 ⊢ T ÷ A.
/2 width=7/ qed.

lemma aaa_tps_conf: ∀L,T1,A. L ⊢ T1 ÷ A → ∀T2,d,e. L ⊢ T1 [d, e] ▶ T2 → L ⊢ T2 ÷ A.
/2 width=7/ qed.
