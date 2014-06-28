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

include "basic_2/substitution/drop_drop.ma".
include "basic_2/static/da.ma".

(* DEGREE ASSIGNMENT FOR TERMS **********************************************)

(* Properties on relocation *************************************************)

lemma da_lift: ∀h,g,G,L1,T1,l. ⦃G, L1⦄ ⊢ T1 ▪[h, g] l →
               ∀L2,s,d,e. ⇩[s, d, e] L2 ≡ L1 → ∀T2. ⇧[d, e] T1 ≡ T2 →
               ⦃G, L2⦄ ⊢ T2 ▪[h, g] l.
#h #g #G #L1 #T1 #l #H elim H -G -L1 -T1 -l
[ #G #L1 #k #l #Hkl #L2 #s #d #e #_ #X #H
  >(lift_inv_sort1 … H) -X /2 width=1 by da_sort/
| #G #L1 #K1 #V1 #i #l #HLK1 #_ #IHV1 #L2 #s #d #e #HL21 #X #H
  elim (lift_inv_lref1 … H) * #Hid #H destruct
  [ elim (drop_trans_le … HL21 … HLK1) -L1 /2 width=2 by lt_to_le/ #X #HLK2 #H
    elim (drop_inv_skip2 … H) -H /2 width=1 by lt_plus_to_minus_r/ -Hid #K2 #V2 #HK21 #HV12 #H destruct
    /3 width=9 by da_ldef/
  | lapply (drop_trans_ge … HL21 … HLK1 ?) -L1
    /3 width=8 by da_ldef, drop_inv_gen/
  ]
| #G #L1 #K1 #W1 #i #l #HLK1 #_ #IHW1 #L2 #s #d #e #HL21 #X #H
  elim (lift_inv_lref1 … H) * #Hid #H destruct
  [ elim (drop_trans_le … HL21 … HLK1) -L1 /2 width=2 by lt_to_le/ #X #HLK2 #H
    elim (drop_inv_skip2 … H) -H /2 width=1 by lt_plus_to_minus_r/ -Hid #K2 #W2 #HK21 #HW12 #H destruct
    /3 width=8 by da_ldec/
  | lapply (drop_trans_ge … HL21 … HLK1 ?) -L1
    /3 width=8 by da_ldec, drop_inv_gen/
  ]
| #a #I #G #L1 #V1 #T1 #l #_ #IHT1 #L2 #s #d #e #HL21 #X #H
  elim (lift_inv_bind1 … H) -H #V2 #T2 #HV12 #HU12 #H destruct
  /4 width=5 by da_bind, drop_skip/
| #I #G #L1 #V1 #T1 #l #_ #IHT1 #L2 #s #d #e #HL21 #X #H
  elim (lift_inv_flat1 … H) -H #V2 #T2 #HV12 #HU12 #H destruct
  /3 width=5 by da_flat/
]
qed.

(* Inversion lemmas on relocation *******************************************)

lemma da_inv_lift: ∀h,g,G,L2,T2,l. ⦃G, L2⦄ ⊢ T2 ▪[h, g] l →
                   ∀L1,s,d,e. ⇩[s, d, e] L2 ≡ L1 → ∀T1. ⇧[d, e] T1 ≡ T2 →
                   ⦃G, L1⦄ ⊢ T1 ▪[h, g] l.
#h #g #G #L2 #T2 #l #H elim H -G -L2 -T2 -l
[ #G #L2 #k #l #Hkl #L1 #s #d #e #_ #X #H
  >(lift_inv_sort2 … H) -X /2 width=1 by da_sort/
| #G #L2 #K2 #V2 #i #l #HLK2 #HV2 #IHV2 #L1 #s #d #e #HL21 #X #H
  elim (lift_inv_lref2 … H) * #Hid #H destruct [ -HV2 | -IHV2 ]
  [ elim (drop_conf_lt … HL21 … HLK2) -L2 /3 width=8 by da_ldef/
  | lapply (drop_conf_ge … HL21 … HLK2 ?) -L2 /2 width=4 by da_ldef/
  ]
| #G #L2 #K2 #W2 #i #l #HLK2 #HW2 #IHW2 #L1 #s #d #e #HL21 #X #H
  elim (lift_inv_lref2 … H) * #Hid #H destruct [ -HW2 | -IHW2 ]
  [ elim (drop_conf_lt … HL21 … HLK2) -L2 /3 width=8 by da_ldec/
  | lapply (drop_conf_ge … HL21 … HLK2 ?) -L2 /2 width=4 by da_ldec/
  ]
| #a #I #G #L2 #V2 #T2 #l #_ #IHT2 #L1 #s #d #e #HL21 #X #H
  elim (lift_inv_bind2 … H) -H #V1 #T1 #HV12 #HT12 #H destruct
  /4 width=5 by da_bind, drop_skip/
| #I #G #L2 #V2 #T2 #l #_ #IHT2 #L1 #s #d #e #HL21 #X #H
  elim (lift_inv_flat2 … H) -H #V1 #T1 #HV12 #HT12 #H destruct
  /3 width=5 by da_flat/
]
qed-.
