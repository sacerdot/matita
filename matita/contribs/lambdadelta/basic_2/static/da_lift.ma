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
include "basic_2/static/da.ma".

(* DEGREE ASSIGNMENT FOR TERMS **********************************************)

(* Properties on relocation *************************************************)

lemma da_lift: ∀h,g,G,L1,T1,l. ⦃G, L1⦄ ⊢ T1 ▪[h, g] l →
               ∀L2,d,e. ⇩[d, e] L2 ≡ L1 → ∀T2. ⇧[d, e] T1 ≡ T2 →
               ⦃G, L2⦄ ⊢ T2 ▪[h, g] l.
#h #g #G #L1 #T1 #l #H elim H -G -L1 -T1 -l
[ #G #L1 #k #l #Hkl #L2 #d #e #_ #X #H
  >(lift_inv_sort1 … H) -X /2 width=1/
| #G #L1 #K1 #V1 #i #l #HLK1 #_ #IHV1 #L2 #d #e #HL21 #X #H
  elim (lift_inv_lref1 … H) * #Hid #H destruct
  [ elim (ldrop_trans_le … HL21 … HLK1) -L1 /2 width=2/ #X #HLK2 #H
    elim (ldrop_inv_skip2 … H) -H /2 width=1/ -Hid #K2 #V2 #HK21 #HV12 #H destruct
    /3 width=7/
  | lapply (ldrop_trans_ge … HL21 … HLK1 ?) -L1 // -Hid /3 width=7/
  ]
| #G #L1 #K1 #W1 #i #l #HLK1 #_ #IHW1 #L2 #d #e #HL21 #X #H
  elim (lift_inv_lref1 … H) * #Hid #H destruct
  [ elim (ldrop_trans_le … HL21 … HLK1) -L1 /2 width=2/ #X #HLK2 #H
    elim (ldrop_inv_skip2 … H) -H /2 width=1/ -Hid #K2 #W2 #HK21 #HW12 #H destruct
    /3 width=7/
  | lapply (ldrop_trans_ge … HL21 … HLK1 ?) -L1 // -Hid /3 width=7/
  ]
| #a #I #G #L1 #V1 #T1 #l #_ #IHT1 #L2 #d #e #HL21 #X #H
  elim (lift_inv_bind1 … H) -H #V2 #T2 #HV12 #HU12 #H destruct /4 width=4/
| #I #G #L1 #V1 #T1 #l #_ #IHT1 #L2 #d #e #HL21 #X #H
  elim (lift_inv_flat1 … H) -H #V2 #T2 #HV12 #HU12 #H destruct /3 width=4/
]
qed.

(* Inversion lemmas on relocation *******************************************)

lemma da_inv_lift: ∀h,g,G,L2,T2,l. ⦃G, L2⦄ ⊢ T2 ▪[h, g] l →
                   ∀L1,d,e. ⇩[d, e] L2 ≡ L1 → ∀T1. ⇧[d, e] T1 ≡ T2 →
                   ⦃G, L1⦄ ⊢ T1 ▪[h, g] l.
#h #g #G #L2 #T2 #l #H elim H -G -L2 -T2 -l
[ #G #L2 #k #l #Hkl #L1 #d #e #_ #X #H
  >(lift_inv_sort2 … H) -X /2 width=1/
| #G #L2 #K2 #V2 #i #l #HLK2 #HV2 #IHV2 #L1 #d #e #HL21 #X #H
  elim (lift_inv_lref2 … H) * #Hid #H destruct [ -HV2 | -IHV2 ]
  [ elim (ldrop_conf_lt … HL21 … HLK2) -L2 // /3 width=7/
  | lapply (ldrop_conf_ge … HL21 … HLK2 ?) -L2 // /2 width=4/
  ]
| #G #L2 #K2 #W2 #i #l #HLK2 #HW2 #IHW2 #L1 #d #e #HL21 #X #H
  elim (lift_inv_lref2 … H) * #Hid #H destruct [ -HW2 | -IHW2 ]
  [ elim (ldrop_conf_lt … HL21 … HLK2) -L2 // /3 width=7/
  | lapply (ldrop_conf_ge … HL21 … HLK2 ?) -L2 // /2 width=4/
  ]
| #a #I #G #L2 #V2 #T2 #l #_ #IHT2 #L1 #d #e #HL21 #X #H
  elim (lift_inv_bind2 … H) -H #V1 #T1 #HV12 #HT12 #H destruct /4 width=4/
| #I #G #L2 #V2 #T2 #l #_ #IHT2 #L1 #d #e #HL21 #X #H
  elim (lift_inv_flat2 … H) -H #V1 #T1 #HV12 #HT12 #H destruct /3 width=4/
]
qed-.
