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

include "basic_2/relocation/drops.ma".
include "basic_2/static/aaa.ma".

(* ATONIC ARITY ASSIGNMENT ON TERMS *****************************************)

(* Properties with generic slicing for local environments *******************)

(* Basic_2A1: was: aaa_lref *)
lemma aaa_lref_gen: ∀I,G,K,V,B,i,L. ⬇*[i] L ≡ K.ⓑ{I}V → ⦃G, K⦄ ⊢ V ⁝ B → ⦃G, L⦄ ⊢ #i ⁝ B.
#I #G #K #V #B #i elim i -i
[ #L #H lapply (drops_fwd_isid … H ?) -H //
  #H destruct /2 width=1 by aaa_zero/
| #i #IH #L <uni_succ #H #HB lapply (drops_inv_pair2_isuni_next … H) -H // *
  #Z #Y #X #HY #H destruct /3 width=1 by aaa_lref/
]
qed.

(* Basic_2A1: includes: aaa_lift *)
lemma aaa_lifts: ∀G,L1,T1,A. ⦃G, L1⦄ ⊢ T1 ⁝ A → ∀L2,c,f. ⬇*[c, f] L2 ≡ L1 →
                 ∀T2. ⬆*[f] T1 ≡ T2 → ⦃G, L2⦄ ⊢ T2 ⁝ A.
#G #L1 #T1 #A #H elim H -G -L1 -T1 -A
[ #G #L1 #s #L2 #c #f #_ #T2 #H
  >(lifts_inv_sort1 … H) -H //
| #I #G #L1 #V1 #B #_ #IHB #L2 #c #f #HL21 #T2 #H
  elim (lifts_inv_lref1 … H) -H #i2 #Hi #H destruct
  @aaa_lref_gen [5: @IHB ]
| #I #G #L1 #V1 #B #i1 #_ #IHB #L2 #c #f #HL21 #T2 #H
  elim (lifts_inv_lref1 … H) -H #i2 #Hi #H destruct
  lapply (at_inv_nxx … H)
  
  
  
  
| #I #G #L1 #K1 #V1 #B #i #HLK1 #_ #IHB #L2 #c #l #k #HL21 #T2 #H
  elim (lift_inv_lref1 … H) -H * #Hil #H destruct
  [ elim (drop_trans_le … HL21 … HLK1) -L1 /2 width=2 by ylt_fwd_le/ #X #HLK2 #H
    elim (drop_inv_skip2 … H) -H /2 width=1 by ylt_to_minus/ -Hil #K2 #V2 #HK21 #HV12 #H destruct
    /3 width=9 by aaa_lref/
  | lapply (drop_trans_ge … HL21 … HLK1 ?) -L1
    /3 width=9 by aaa_lref, drop_inv_gen/
  ]
| #a #G #L1 #V1 #T1 #B #A #_ #_ #IHB #IHA #L2 #c #l #k #HL21 #X #H
  elim (lift_inv_bind1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct
  /4 width=5 by aaa_abbr, drop_skip/
| #a #G #L1 #V1 #T1 #B #A #_ #_ #IHB #IHA #L2 #c #l #k #HL21 #X #H
  elim (lift_inv_bind1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct
  /4 width=5 by aaa_abst, drop_skip/
| #G #L1 #V1 #T1 #B #A #_ #_ #IHB #IHA #L2 #c #l #k #HL21 #X #H
  elim (lift_inv_flat1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct
  /3 width=5 by aaa_appl/
| #G #L1 #V1 #T1 #A #_ #_ #IH1 #IH2 #L2 #c #l #k #HL21 #X #H
  elim (lift_inv_flat1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct
  /3 width=5 by aaa_cast/
]
qed.

(* Inversion lemmas with generic slicing for local environments *************)

(* Basic_2A1: was: aaa_inv_lref *)
lemma aaa_inv_lref_gen: ∀G,A,i,L. ⦃G, L⦄ ⊢ #i ⁝ A →
                        ∃∃I,K,V. ⬇*[i] L ≡ K.ⓑ{I}V & ⦃G, K⦄ ⊢ V ⁝ A.
#G #A #i elim i -i
[ #L #H elim (aaa_inv_zero … H) -H /3 width=5 by drops_refl, ex2_3_intro/
| #i #IH #L #H elim (aaa_inv_lref … H) -H
  #I #K #V #H #HA destruct elim (IH … HA) -IH -HA /3 width=5 by drops_drop, ex2_3_intro/
]
qed-.

lemma aaa_inv_lift: ∀G,L2,T2,A. ⦃G, L2⦄ ⊢ T2 ⁝ A → ∀L1,c,l,k. ⬇[c, l, k] L2 ≡ L1 →
                    ∀T1. ⬆[l, k] T1 ≡ T2 → ⦃G, L1⦄ ⊢ T1 ⁝ A.
#G #L2 #T2 #A #H elim H -G -L2 -T2 -A
[ #G #L2 #s #L1 #c #l #k #_ #T1 #H
  >(lift_inv_sort2 … H) -H //
| #I #G #L2 #K2 #V2 #B #i #HLK2 #_ #IHB #L1 #c #l #k #HL21 #T1 #H
  elim (lift_inv_lref2 … H) -H * #Hil #H destruct
  [ elim (drop_conf_lt … HL21 … HLK2) -L2 /3 width=9 by aaa_lref/
  | lapply (drop_conf_ge … HL21 … HLK2 ?) -L2 /3 width=9 by aaa_lref/
  ]
| #a #G #L2 #V2 #T2 #B #A #_ #_ #IHB #IHA #L1 #c #l #k #HL21 #X #H
  elim (lift_inv_bind2 … H) -H #V1 #T1 #HV12 #HT12 #H destruct
  /4 width=5 by aaa_abbr, drop_skip/
| #a #G #L2 #V2 #T2 #B #A #_ #_ #IHB #IHA #L1 #c #l #k #HL21 #X #H
  elim (lift_inv_bind2 … H) -H #V1 #T1 #HV12 #HT12 #H destruct
  /4 width=5 by aaa_abst, drop_skip/
| #G #L2 #V2 #T2 #B #A #_ #_ #IHB #IHA #L1 #c #l #k #HL21 #X #H
  elim (lift_inv_flat2 … H) -H #V1 #T1 #HV12 #HT12 #H destruct
  /3 width=5 by aaa_appl/
| #G #L2 #V2 #T2 #A #_ #_ #IH1 #IH2 #L1 #c #l #k #HL21 #X #H
  elim (lift_inv_flat2 … H) -H #V1 #T1 #HV12 #HT12 #H destruct
  /3 width=5 by aaa_cast/
]
qed-.
