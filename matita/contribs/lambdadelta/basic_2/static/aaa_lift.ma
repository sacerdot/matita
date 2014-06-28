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
include "basic_2/static/aaa.ma".

(* ATONIC ARITY ASSIGNMENT ON TERMS *****************************************)

(* Properties on basic relocation *******************************************)

lemma aaa_lift: ∀G,L1,T1,A. ⦃G, L1⦄ ⊢ T1 ⁝ A → ∀L2,s,d,e. ⇩[s, d, e] L2 ≡ L1 →
                ∀T2. ⇧[d, e] T1 ≡ T2 → ⦃G, L2⦄ ⊢ T2 ⁝ A.
#G #L1 #T1 #A #H elim H -G -L1 -T1 -A
[ #G #L1 #k #L2 #s #d #e #_ #T2 #H
  >(lift_inv_sort1 … H) -H //
| #I #G #L1 #K1 #V1 #B #i #HLK1 #_ #IHB #L2 #s #d #e #HL21 #T2 #H
  elim (lift_inv_lref1 … H) -H * #Hid #H destruct
  [ elim (drop_trans_le … HL21 … HLK1) -L1 /2 width=2 by lt_to_le/ #X #HLK2 #H
    elim (drop_inv_skip2 … H) -H /2 width=1 by lt_plus_to_minus_r/ -Hid #K2 #V2 #HK21 #HV12 #H destruct
    /3 width=9 by aaa_lref/
  | lapply (drop_trans_ge … HL21 … HLK1 ?) -L1
    /3 width=9 by aaa_lref, drop_inv_gen/
  ]
| #a #G #L1 #V1 #T1 #B #A #_ #_ #IHB #IHA #L2 #s #d #e #HL21 #X #H
  elim (lift_inv_bind1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct
  /4 width=5 by aaa_abbr, drop_skip/
| #a #G #L1 #V1 #T1 #B #A #_ #_ #IHB #IHA #L2 #s #d #e #HL21 #X #H
  elim (lift_inv_bind1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct
  /4 width=5 by aaa_abst, drop_skip/
| #G #L1 #V1 #T1 #B #A #_ #_ #IHB #IHA #L2 #s #d #e #HL21 #X #H
  elim (lift_inv_flat1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct
  /3 width=5 by aaa_appl/
| #G #L1 #V1 #T1 #A #_ #_ #IH1 #IH2 #L2 #s #d #e #HL21 #X #H
  elim (lift_inv_flat1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct
  /3 width=5 by aaa_cast/
]
qed.

lemma aaa_inv_lift: ∀G,L2,T2,A. ⦃G, L2⦄ ⊢ T2 ⁝ A → ∀L1,s,d,e. ⇩[s, d, e] L2 ≡ L1 →
                    ∀T1. ⇧[d, e] T1 ≡ T2 → ⦃G, L1⦄ ⊢ T1 ⁝ A.
#G #L2 #T2 #A #H elim H -G -L2 -T2 -A
[ #G #L2 #k #L1 #s #d #e #_ #T1 #H
  >(lift_inv_sort2 … H) -H //
| #I #G #L2 #K2 #V2 #B #i #HLK2 #_ #IHB #L1 #s #d #e #HL21 #T1 #H
  elim (lift_inv_lref2 … H) -H * #Hid #H destruct
  [ elim (drop_conf_lt … HL21 … HLK2) -L2 /3 width=9 by aaa_lref/
  | lapply (drop_conf_ge … HL21 … HLK2 ?) -L2 /3 width=9 by aaa_lref/
  ]
| #a #G #L2 #V2 #T2 #B #A #_ #_ #IHB #IHA #L1 #s #d #e #HL21 #X #H
  elim (lift_inv_bind2 … H) -H #V1 #T1 #HV12 #HT12 #H destruct
  /4 width=5 by aaa_abbr, drop_skip/
| #a #G #L2 #V2 #T2 #B #A #_ #_ #IHB #IHA #L1 #s #d #e #HL21 #X #H
  elim (lift_inv_bind2 … H) -H #V1 #T1 #HV12 #HT12 #H destruct
  /4 width=5 by aaa_abst, drop_skip/
| #G #L2 #V2 #T2 #B #A #_ #_ #IHB #IHA #L1 #s #d #e #HL21 #X #H
  elim (lift_inv_flat2 … H) -H #V1 #T1 #HV12 #HT12 #H destruct
  /3 width=5 by aaa_appl/
| #G #L2 #V2 #T2 #A #_ #_ #IH1 #IH2 #L1 #s #d #e #HL21 #X #H
  elim (lift_inv_flat2 … H) -H #V1 #T1 #HV12 #HT12 #H destruct
  /3 width=5 by aaa_cast/
]
qed-.
