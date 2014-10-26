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

include "basic_2/substitution/cpy_lift.ma".
include "basic_2/multiple/cpys.ma".

(* CONTEXT-SENSITIVE EXTENDED MULTIPLE SUBSTITUTION FOR TERMS ***************)

(* Advanced properties ******************************************************)

lemma cpys_subst: ∀I,G,L,K,V,U1,i,l,m.
                  l ≤ yinj i → i < l + m →
                  ⬇[i] L ≡ K.ⓑ{I}V → ⦃G, K⦄ ⊢ V ▶*[0, ⫰(l+m-i)] U1 →
                  ∀U2. ⬆[0, i+1] U1 ≡ U2 → ⦃G, L⦄ ⊢ #i ▶*[l, m] U2.
#I #G #L #K #V #U1 #i #l #m #Hli #Hilm #HLK #H @(cpys_ind … H) -U1
[ /3 width=5 by cpy_cpys, cpy_subst/
| #U #U1 #_ #HU1 #IHU #U2 #HU12
  elim (lift_total U 0 (i+1)) #U0 #HU0
  lapply (IHU … HU0) -IHU #H
  lapply (drop_fwd_drop2 … HLK) -HLK #HLK
  lapply (cpy_lift_ge … HU1 … HLK HU0 HU12 ?) -HU1 -HLK -HU0 -HU12 // #HU02
  lapply (cpy_weak … HU02 l m ? ?) -HU02
  [2,3: /2 width=3 by cpys_strap1, yle_succ_dx/ ]
  >yplus_O1 <yplus_inj >ymax_pre_sn_comm /2 width=1 by ylt_fwd_le_succ/
]
qed.

lemma cpys_subst_Y2: ∀I,G,L,K,V,U1,i,l.
                     l ≤ yinj i →
                     ⬇[i] L ≡ K.ⓑ{I}V → ⦃G, K⦄ ⊢ V ▶*[0, ∞] U1 →
                     ∀U2. ⬆[0, i+1] U1 ≡ U2 → ⦃G, L⦄ ⊢ #i ▶*[l, ∞] U2.
#I #G #L #K #V #U1 #i #l #Hli #HLK #HVU1 #U2 #HU12
@(cpys_subst … HLK … HU12) >yminus_Y_inj //
qed.

(* Advanced inversion lemmas *************************************************)

lemma cpys_inv_atom1: ∀I,G,L,T2,l,m. ⦃G, L⦄ ⊢ ⓪{I} ▶*[l, m] T2 →
                      T2 = ⓪{I} ∨
                      ∃∃J,K,V1,V2,i. l ≤ yinj i & i < l + m &
                                    ⬇[i] L ≡ K.ⓑ{J}V1 &
                                     ⦃G, K⦄ ⊢ V1 ▶*[0, ⫰(l+m-i)] V2 &
                                     ⬆[O, i+1] V2 ≡ T2 &
                                     I = LRef i.
#I #G #L #T2 #l #m #H @(cpys_ind … H) -T2
[ /2 width=1 by or_introl/
| #T #T2 #_ #HT2 *
  [ #H destruct
    elim (cpy_inv_atom1 … HT2) -HT2 [ /2 width=1 by or_introl/ | * /3 width=11 by ex6_5_intro, or_intror/ ]
  | * #J #K #V1 #V #i #Hli #Hilm #HLK #HV1 #HVT #HI
    lapply (drop_fwd_drop2 … HLK) #H
    elim (cpy_inv_lift1_ge_up … HT2 … H … HVT) -HT2 -H -HVT
    [2,3,4: /2 width=1 by ylt_fwd_le_succ, yle_succ_dx/ ]
    /4 width=11 by cpys_strap1, ex6_5_intro, or_intror/
  ]
]
qed-.

lemma cpys_inv_lref1: ∀G,L,T2,i,l,m. ⦃G, L⦄ ⊢ #i ▶*[l, m] T2 →
                      T2 = #i ∨
                      ∃∃I,K,V1,V2. l ≤ i & i < l + m &
                                   ⬇[i] L ≡ K.ⓑ{I}V1 &
                                   ⦃G, K⦄ ⊢ V1 ▶*[0, ⫰(l+m-i)] V2 &
                                   ⬆[O, i+1] V2 ≡ T2.
#G #L #T2 #i #l #m #H elim (cpys_inv_atom1 … H) -H /2 width=1 by or_introl/
* #I #K #V1 #V2 #j #Hlj #Hjlm #HLK #HV12 #HVT2 #H destruct /3 width=7 by ex5_4_intro, or_intror/
qed-.

lemma cpys_inv_lref1_Y2: ∀G,L,T2,i,l. ⦃G, L⦄ ⊢ #i ▶*[l, ∞] T2 →
                         T2 = #i ∨
                         ∃∃I,K,V1,V2. l ≤ i & ⬇[i] L ≡ K.ⓑ{I}V1 &
                                      ⦃G, K⦄ ⊢ V1 ▶*[0, ∞] V2 & ⬆[O, i+1] V2 ≡ T2.
#G #L #T2 #i #l #H elim (cpys_inv_lref1 … H) -H /2 width=1 by or_introl/
* >yminus_Y_inj /3 width=7 by or_intror, ex4_4_intro/
qed-.

lemma cpys_inv_lref1_drop: ∀G,L,T2,i,l,m. ⦃G, L⦄ ⊢ #i ▶*[l, m] T2 →
                            ∀I,K,V1. ⬇[i] L ≡ K.ⓑ{I}V1 →
                            ∀V2. ⬆[O, i+1] V2 ≡ T2 →
                            ∧∧ ⦃G, K⦄ ⊢ V1 ▶*[0, ⫰(l+m-i)] V2
                             & l ≤ i
                             & i < l + m.
#G #L #T2 #i #l #m #H #I #K #V1 #HLK #V2 #HVT2 elim (cpys_inv_lref1 … H) -H
[ #H destruct elim (lift_inv_lref2_be … HVT2) -HVT2 -HLK //
| * #Z #Y #X1 #X2 #Hli #Hilm #HLY #HX12 #HXT2
  lapply (lift_inj … HXT2 … HVT2) -T2 #H destruct
  lapply (drop_mono … HLY … HLK) -L #H destruct
  /2 width=1 by and3_intro/
]
qed-.

(* Properties on relocation *************************************************)

lemma cpys_lift_le: ∀G,K,T1,T2,lt,mt. ⦃G, K⦄ ⊢ T1 ▶*[lt, mt] T2 →
                    ∀L,U1,s,l,m. lt + mt ≤ yinj l → ⬇[s, l, m] L ≡ K →
                    ⬆[l, m] T1 ≡ U1 → ∀U2. ⬆[l, m] T2 ≡ U2 →
                    ⦃G, L⦄ ⊢ U1 ▶*[lt, mt] U2.
#G #K #T1 #T2 #lt #mt #H #L #U1 #s #l #m #Hlmtl #HLK #HTU1 @(cpys_ind … H) -T2
[ #U2 #H >(lift_mono … HTU1 … H) -H //
| -HTU1 #T #T2 #_ #HT2 #IHT #U2 #HTU2
  elim (lift_total T l m) #U #HTU
  lapply (IHT … HTU) -IHT #HU1
  lapply (cpy_lift_le … HT2 … HLK HTU HTU2 ?) -HT2 -HLK -HTU -HTU2 /2 width=3 by cpys_strap1/
]
qed-.

lemma cpys_lift_be: ∀G,K,T1,T2,lt,mt. ⦃G, K⦄ ⊢ T1 ▶*[lt, mt] T2 →
                    ∀L,U1,s,l,m. lt ≤ yinj l → l ≤ lt + mt →
                    ⬇[s, l, m] L ≡ K → ⬆[l, m] T1 ≡ U1 →
                    ∀U2. ⬆[l, m] T2 ≡ U2 → ⦃G, L⦄ ⊢ U1 ▶*[lt, mt + m] U2.
#G #K #T1 #T2 #lt #mt #H #L #U1 #s #l #m #Hltl #Hllmt #HLK #HTU1 @(cpys_ind … H) -T2
[ #U2 #H >(lift_mono … HTU1 … H) -H //
| -HTU1 #T #T2 #_ #HT2 #IHT #U2 #HTU2
  elim (lift_total T l m) #U #HTU
  lapply (IHT … HTU) -IHT #HU1
  lapply (cpy_lift_be … HT2 … HLK HTU HTU2 ? ?) -HT2 -HLK -HTU -HTU2 /2 width=3 by cpys_strap1/
]
qed-.

lemma cpys_lift_ge: ∀G,K,T1,T2,lt,mt. ⦃G, K⦄ ⊢ T1 ▶*[lt, mt] T2 →
                    ∀L,U1,s,l,m. yinj l ≤ lt → ⬇[s, l, m] L ≡ K →
                    ⬆[l, m] T1 ≡ U1 → ∀U2. ⬆[l, m] T2 ≡ U2 →
                    ⦃G, L⦄ ⊢ U1 ▶*[lt+m, mt] U2.
#G #K #T1 #T2 #lt #mt #H #L #U1 #s #l #m #Hllt #HLK #HTU1 @(cpys_ind … H) -T2
[ #U2 #H >(lift_mono … HTU1 … H) -H //
| -HTU1 #T #T2 #_ #HT2 #IHT #U2 #HTU2
  elim (lift_total T l m) #U #HTU
  lapply (IHT … HTU) -IHT #HU1
  lapply (cpy_lift_ge … HT2 … HLK HTU HTU2 ?) -HT2 -HLK -HTU -HTU2 /2 width=3 by cpys_strap1/
]
qed-.

(* Inversion lemmas for relocation ******************************************)

lemma cpys_inv_lift1_le: ∀G,L,U1,U2,lt,mt. ⦃G, L⦄ ⊢ U1 ▶*[lt, mt] U2 →
                         ∀K,s,l,m. ⬇[s, l, m] L ≡ K → ∀T1. ⬆[l, m] T1 ≡ U1 →
                         lt + mt ≤ l →
                         ∃∃T2. ⦃G, K⦄ ⊢ T1 ▶*[lt, mt] T2 & ⬆[l, m] T2 ≡ U2.
#G #L #U1 #U2 #lt #mt #H #K #s #l #m #HLK #T1 #HTU1 #Hlmtl @(cpys_ind … H) -U2
[ /2 width=3 by ex2_intro/
| -HTU1 #U #U2 #_ #HU2 * #T #HT1 #HTU
  elim (cpy_inv_lift1_le … HU2 … HLK … HTU) -HU2 -HLK -HTU /3 width=3 by cpys_strap1, ex2_intro/
]
qed-.

lemma cpys_inv_lift1_be: ∀G,L,U1,U2,lt,mt. ⦃G, L⦄ ⊢ U1 ▶*[lt, mt] U2 →
                         ∀K,s,l,m. ⬇[s, l, m] L ≡ K → ∀T1. ⬆[l, m] T1 ≡ U1 →
                         lt ≤ l → yinj l + m ≤ lt + mt →
                         ∃∃T2. ⦃G, K⦄ ⊢ T1 ▶*[lt, mt - m] T2 & ⬆[l, m] T2 ≡ U2.
#G #L #U1 #U2 #lt #mt #H #K #s #l #m #HLK #T1 #HTU1 #Hltl #Hlmlmt @(cpys_ind … H) -U2
[ /2 width=3 by ex2_intro/
| -HTU1 #U #U2 #_ #HU2 * #T #HT1 #HTU
  elim (cpy_inv_lift1_be … HU2 … HLK … HTU) -HU2 -HLK -HTU /3 width=3 by cpys_strap1, ex2_intro/
]
qed-.

lemma cpys_inv_lift1_ge: ∀G,L,U1,U2,lt,mt. ⦃G, L⦄ ⊢ U1 ▶*[lt, mt] U2 →
                         ∀K,s,l,m. ⬇[s, l, m] L ≡ K → ∀T1. ⬆[l, m] T1 ≡ U1 →
                         yinj l + m ≤ lt →
                         ∃∃T2. ⦃G, K⦄ ⊢ T1 ▶*[lt - m, mt] T2 & ⬆[l, m] T2 ≡ U2.
#G #L #U1 #U2 #lt #mt #H #K #s #l #m #HLK #T1 #HTU1 #Hlmlt @(cpys_ind … H) -U2
[ /2 width=3 by ex2_intro/
| -HTU1 #U #U2 #_ #HU2 * #T #HT1 #HTU
  elim (cpy_inv_lift1_ge … HU2 … HLK … HTU) -HU2 -HLK -HTU /3 width=3 by cpys_strap1, ex2_intro/
]
qed-.

(* Advanced inversion lemmas on relocation **********************************)

lemma cpys_inv_lift1_ge_up: ∀G,L,U1,U2,lt,mt. ⦃G, L⦄ ⊢ U1 ▶*[lt, mt] U2 →
                            ∀K,s,l,m. ⬇[s, l, m] L ≡ K → ∀T1. ⬆[l, m] T1 ≡ U1 →
                            l ≤ lt → lt ≤ yinj l + m → yinj l + m ≤ lt + mt →
                            ∃∃T2. ⦃G, K⦄ ⊢ T1 ▶*[l, lt + mt - (yinj l + m)] T2 &
                                 ⬆[l, m] T2 ≡ U2.
#G #L #U1 #U2 #lt #mt #H #K #s #l #m #HLK #T1 #HTU1 #Hllt #Hltlm #Hlmlmt @(cpys_ind … H) -U2
[ /2 width=3 by ex2_intro/
| -HTU1 #U #U2 #_ #HU2 * #T #HT1 #HTU
  elim (cpy_inv_lift1_ge_up … HU2 … HLK … HTU) -HU2 -HLK -HTU /3 width=3 by cpys_strap1, ex2_intro/
]
qed-.

lemma cpys_inv_lift1_be_up: ∀G,L,U1,U2,lt,mt. ⦃G, L⦄ ⊢ U1 ▶*[lt, mt] U2 →
                            ∀K,s,l,m. ⬇[s, l, m] L ≡ K → ∀T1. ⬆[l, m] T1 ≡ U1 →
                            lt ≤ l → lt + mt ≤ yinj l + m →
                            ∃∃T2. ⦃G, K⦄ ⊢ T1 ▶*[lt, l - lt] T2 & ⬆[l, m] T2 ≡ U2.
#G #L #U1 #U2 #lt #mt #H #K #s #l #m #HLK #T1 #HTU1 #Hltl #Hlmtlm @(cpys_ind … H) -U2
[ /2 width=3 by ex2_intro/
| -HTU1 #U #U2 #_ #HU2 * #T #HT1 #HTU
  elim (cpy_inv_lift1_be_up … HU2 … HLK … HTU) -HU2 -HLK -HTU /3 width=3 by cpys_strap1, ex2_intro/
]
qed-.

lemma cpys_inv_lift1_le_up: ∀G,L,U1,U2,lt,mt. ⦃G, L⦄ ⊢ U1 ▶*[lt, mt] U2 →
                            ∀K,s,l,m. ⬇[s, l, m] L ≡ K → ∀T1. ⬆[l, m] T1 ≡ U1 →
                            lt ≤ l → l ≤ lt + mt → lt + mt ≤ yinj l + m →
                            ∃∃T2. ⦃G, K⦄ ⊢ T1 ▶*[lt, l - lt] T2 & ⬆[l, m] T2 ≡ U2.
#G #L #U1 #U2 #lt #mt #H #K #s #l #m #HLK #T1 #HTU1 #Hltl #Hllmt #Hlmtlm @(cpys_ind … H) -U2
[ /2 width=3 by ex2_intro/
| -HTU1 #U #U2 #_ #HU2 * #T #HT1 #HTU
  elim (cpy_inv_lift1_le_up … HU2 … HLK … HTU) -HU2 -HLK -HTU /3 width=3 by cpys_strap1, ex2_intro/
]
qed-.

lemma cpys_inv_lift1_subst: ∀G,L,W1,W2,l,m. ⦃G, L⦄ ⊢ W1 ▶*[l, m] W2 →
                            ∀K,V1,i. ⬇[i+1] L ≡ K → ⬆[O, i+1] V1 ≡ W1 → 
                            l ≤ yinj i → i < l + m →
                            ∃∃V2.  ⦃G, K⦄ ⊢ V1 ▶*[O, ⫰(l+m-i)] V2 & ⬆[O, i+1] V2 ≡ W2.
#G #L #W1 #W2 #l #m #HW12 #K #V1 #i #HLK #HVW1 #Hli #Hilm
elim (cpys_inv_lift1_ge_up … HW12 … HLK … HVW1 ? ? ?) //
>yplus_O1 <yplus_inj >yplus_SO2
[ >yminus_succ2 /2 width=3 by ex2_intro/
| /2 width=1 by ylt_fwd_le_succ1/
| /2 width=3 by yle_trans/
]
qed-.
