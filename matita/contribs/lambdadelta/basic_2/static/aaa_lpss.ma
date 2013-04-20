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

include "basic_2/substitution/lpss_ldrop.ma".
include "basic_2/static/aaa_lift.ma".

(* ATONIC ARITY ASSIGNMENT ON TERMS *****************************************)

(* Properties about sn parallel substitution ********************************)

(* Note: lemma 500 *)
lemma aaa_cpss_lpss_conf: ∀L1,T1,A. L1 ⊢ T1 ⁝ A → ∀T2. L1 ⊢ T1 ▶* T2 →
                          ∀L2. L1 ⊢ ▶* L2 → L2 ⊢ T2 ⁝ A.
#L1 #T1 #A #H elim H -L1 -T1 -A
[ #L1 #k #X #H
  >(cpss_inv_sort1 … H) -H //
| #I #L1 #K1 #V1 #B #i #HLK1 #_ #IHV1 #X #H #L2 #HL12
  elim (cpss_inv_lref1 … H) -H
  [ #H destruct
    elim (lpss_ldrop_conf … HLK1 … HL12) -L1 #X #H #HLK2
    elim (lpss_inv_pair1 … H) -H #K2 #V2 #HK12 #HV12 #H destruct /3 width=6/
  | * #Y #Z #V2 #H #HV12 #HV2
    lapply (ldrop_mono … H … HLK1) -H #H destruct
    elim (lpss_ldrop_conf … HLK1 … HL12) -L1 #Z #H #HLK2
    elim (lpss_inv_pair1 … H) -H #K2 #V0 #HK12 #_ #H destruct
    lapply (ldrop_fwd_ldrop2 … HLK2) -V0 /3 width=7/
  ]
| #a #L1 #V1 #T1 #B #A #_ #_ #IHV1 #IHT1 #X #H #L2 #HL12
  elim (cpss_inv_bind1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct /4 width=2/
| #a #L1 #V1 #T1 #B #A #_ #_ #IHV1 #IHT1 #X #H #L2 #HL12
  elim (cpss_inv_bind1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct /4 width=1/
| #L1 #V1 #T1 #B #A #_ #_ #IHV1 #IHT1 #X #H #L2 #HL12
  elim (cpss_inv_flat1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct /3 width=3/
| #L1 #V1 #T1 #A #_ #_ #IHV1 #IHT1 #X #H #L2 #HL12
  elim (cpss_inv_flat1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct /3 width=1/
]
qed-.

lemma aaa_cpss_conf: ∀L,T1,A. L ⊢ T1 ⁝ A → ∀T2. L ⊢ T1 ▶* T2 → L ⊢ T2 ⁝ A.
/2 width=5 by aaa_cpss_lpss_conf/ qed-.

lemma aaa_lpss_conf: ∀L1,T,A. L1 ⊢ T ⁝ A → ∀L2. L1 ⊢ ▶* L2 → L2 ⊢ T ⁝ A.
/2 width=5 by aaa_cpss_lpss_conf/ qed-.
