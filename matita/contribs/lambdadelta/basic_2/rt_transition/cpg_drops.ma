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
include "basic_2/rt_transition/cpg.ma".

(* CONTEXT-SENSITIVE GENERIC PARALLEL RT-TRANSITION FOR TERMS ***************)

(* Properties with generic slicing for local environments *******************)

lemma cpg_delift: ∀h,r,I,G,K,V,T1,L,l. ⬇*[i] L ≡ (K.ⓑ{I}V) →
                  ∃∃T2,T. ⦃G, L⦄ ⊢ T1 ➡[h, 𝟘𝟘] T2 & ⬆*[↑1] T ≡ T2.
#h #r #I #G #K #V #T1 elim T1 -T1
[ * #i #L #l /2 width=4 by cpg_atom, lift_sort, lift_gref, ex2_2_intro/
  elim (lt_or_eq_or_gt i l) #Hil [1,3: /4 width=4 by cpg_atom, lift_lref_ge_minus, lift_lref_lt, ylt_inj, yle_inj, ex2_2_intro/ ]
  destruct
  elim (lift_total V 0 (i+1)) #W #HVW
  elim (lift_split … HVW i i) /3 width=7 by cpg_delta, ex2_2_intro/
| * [ #a ] #I #W1 #U1 #IHW1 #IHU1 #L #l #HLK
  elim (IHW1 … HLK) -IHW1 #W2 #W #HW12 #HW2
  [ elim (IHU1 (L. ⓑ{I} W1) (l+1)) -IHU1 /3 width=9 by cpg_bind, drop_drop, lift_bind, ex2_2_intro/
  | elim (IHU1 … HLK) -IHU1 -HLK /3 width=8 by cpg_flat, lift_flat, ex2_2_intro/
  ]
]
qed-.

lemma cpg_inv_lref1: ∀h,r,G,L,T2,i. ⦃G, L⦄ ⊢ #i ➡[h, r] T2 →
                     T2 = #i ∨
                     ∃∃I,K,V,V2. ⬇[i] L ≡ K. ⓑ{I}V & ⦃G, K⦄ ⊢ V ➡[h, r] V2 &
                                 ⬆[O, i+1] V2 ≡ T2.
#h #r #G #L #T2 #i #H
elim (cpg_inv_atom1 … H) -H /2 width=1 by or_introl/ *
[ #s #d #_ #_ #H destruct
| #I #K #V #V2 #j #HLK #HV2 #HVT2 #H destruct /3 width=7 by ex3_4_intro, or_intror/
]
qed-.
