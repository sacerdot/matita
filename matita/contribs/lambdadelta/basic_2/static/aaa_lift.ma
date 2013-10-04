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

include "basic_2/relocation/ldrop_ldrop.ma".
include "basic_2/static/aaa.ma".

(* ATONIC ARITY ASSIGNMENT ON TERMS *****************************************)

(* Properties concerning basic relocation ***********************************)

lemma aaa_lift: ∀G,L1,T1,A. ⦃G, L1⦄ ⊢ T1 ⁝ A → ∀L2,d,e. ⇩[d, e] L2 ≡ L1 →
                ∀T2. ⇧[d, e] T1 ≡ T2 → ⦃G, L2⦄ ⊢ T2 ⁝ A.
#G #L1 #T1 #A #H elim H -G -L1 -T1 -A
[ #G #L1 #k #L2 #d #e #_ #T2 #H
  >(lift_inv_sort1 … H) -H //
| #I #G #L1 #K1 #V1 #B #i #HLK1 #_ #IHB #L2 #d #e #HL21 #T2 #H
  elim (lift_inv_lref1 … H) -H * #Hid #H destruct
  [ elim (ldrop_trans_le … HL21 … HLK1) -L1 /2 width=2/ #X #HLK2 #H
    elim (ldrop_inv_skip2 … H) -H /2 width=1/ -Hid #K2 #V2 #HK21 #HV12 #H destruct
    /3 width=8/
  | lapply (ldrop_trans_ge … HL21 … HLK1 ?) -L1 // -Hid /3 width=8/
  ]
| #a #G #L1 #V1 #T1 #B #A #_ #_ #IHB #IHA #L2 #d #e #HL21 #X #H
  elim (lift_inv_bind1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct
  /4 width=4/
| #a #G #L1 #V1 #T1 #B #A #_ #_ #IHB #IHA #L2 #d #e #HL21 #X #H
  elim (lift_inv_bind1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct
  /4 width=4/
| #G #L1 #V1 #T1 #B #A #_ #_ #IHB #IHA #L2 #d #e #HL21 #X #H
  elim (lift_inv_flat1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct
  /3 width=4/
| #G #L1 #V1 #T1 #A #_ #_ #IH1 #IH2 #L2 #d #e #HL21 #X #H
  elim (lift_inv_flat1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct
  /3 width=4/
]
qed.

lemma aaa_inv_lift: ∀G,L2,T2,A. ⦃G, L2⦄ ⊢ T2 ⁝ A → ∀L1,d,e. ⇩[d, e] L2 ≡ L1 →
                    ∀T1. ⇧[d, e] T1 ≡ T2 → ⦃G, L1⦄ ⊢ T1 ⁝ A.
#G #L2 #T2 #A #H elim H -G -L2 -T2 -A
[ #G #L2 #k #L1 #d #e #_ #T1 #H
  >(lift_inv_sort2 … H) -H //
| #I #G #L2 #K2 #V2 #B #i #HLK2 #_ #IHB #L1 #d #e #HL21 #T1 #H
  elim (lift_inv_lref2 … H) -H * #Hid #H destruct
  [ elim (ldrop_conf_lt … HL21 … HLK2) -L2 // -Hid /3 width=8/
  | lapply (ldrop_conf_ge … HL21 … HLK2 ?) -L2 // -Hid /3 width=8/
  ]
| #a #G #L2 #V2 #T2 #B #A #_ #_ #IHB #IHA #L1 #d #e #HL21 #X #H
  elim (lift_inv_bind2 … H) -H #V1 #T1 #HV12 #HT12 #H destruct
  /4 width=4/
| #a #G #L2 #V2 #T2 #B #A #_ #_ #IHB #IHA #L1 #d #e #HL21 #X #H
  elim (lift_inv_bind2 … H) -H #V1 #T1 #HV12 #HT12 #H destruct
  /4 width=4/
| #G #L2 #V2 #T2 #B #A #_ #_ #IHB #IHA #L1 #d #e #HL21 #X #H
  elim (lift_inv_flat2 … H) -H #V1 #T1 #HV12 #HT12 #H destruct
  /3 width=4/
| #G #L2 #V2 #T2 #A #_ #_ #IH1 #IH2 #L1 #d #e #HL21 #X #H
  elim (lift_inv_flat2 … H) -H #V1 #T1 #HV12 #HT12 #H destruct
  /3 width=4/
]
qed-.
