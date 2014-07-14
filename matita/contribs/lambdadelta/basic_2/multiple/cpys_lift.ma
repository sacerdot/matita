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

lemma cpys_subst: ∀I,G,L,K,V,U1,i,d,e.
                  d ≤ yinj i → i < d + e →
                  ⇩[i] L ≡ K.ⓑ{I}V → ⦃G, K⦄ ⊢ V ▶*[0, ⫰(d+e-i)] U1 →
                  ∀U2. ⇧[0, i+1] U1 ≡ U2 → ⦃G, L⦄ ⊢ #i ▶*[d, e] U2.
#I #G #L #K #V #U1 #i #d #e #Hdi #Hide #HLK #H @(cpys_ind … H) -U1
[ /3 width=5 by cpy_cpys, cpy_subst/
| #U #U1 #_ #HU1 #IHU #U2 #HU12
  elim (lift_total U 0 (i+1)) #U0 #HU0
  lapply (IHU … HU0) -IHU #H
  lapply (drop_fwd_drop2 … HLK) -HLK #HLK
  lapply (cpy_lift_ge … HU1 … HLK HU0 HU12 ?) -HU1 -HLK -HU0 -HU12 // #HU02
  lapply (cpy_weak … HU02 d e ? ?) -HU02
  [2,3: /2 width=3 by cpys_strap1, yle_succ_dx/ ]
  >yplus_O1 <yplus_inj >ymax_pre_sn_comm /2 width=1 by ylt_fwd_le_succ/
]
qed.

lemma cpys_subst_Y2: ∀I,G,L,K,V,U1,i,d.
                     d ≤ yinj i →
                     ⇩[i] L ≡ K.ⓑ{I}V → ⦃G, K⦄ ⊢ V ▶*[0, ∞] U1 →
                     ∀U2. ⇧[0, i+1] U1 ≡ U2 → ⦃G, L⦄ ⊢ #i ▶*[d, ∞] U2.
#I #G #L #K #V #U1 #i #d #Hdi #HLK #HVU1 #U2 #HU12
@(cpys_subst … HLK … HU12) >yminus_Y_inj //
qed.

(* Advanced inversion lemmas *************************************************)

lemma cpys_inv_atom1: ∀I,G,L,T2,d,e. ⦃G, L⦄ ⊢ ⓪{I} ▶*[d, e] T2 →
                      T2 = ⓪{I} ∨
                      ∃∃J,K,V1,V2,i. d ≤ yinj i & i < d + e &
                                    ⇩[i] L ≡ K.ⓑ{J}V1 &
                                     ⦃G, K⦄ ⊢ V1 ▶*[0, ⫰(d+e-i)] V2 &
                                     ⇧[O, i+1] V2 ≡ T2 &
                                     I = LRef i.
#I #G #L #T2 #d #e #H @(cpys_ind … H) -T2
[ /2 width=1 by or_introl/
| #T #T2 #_ #HT2 *
  [ #H destruct
    elim (cpy_inv_atom1 … HT2) -HT2 [ /2 width=1 by or_introl/ | * /3 width=11 by ex6_5_intro, or_intror/ ]
  | * #J #K #V1 #V #i #Hdi #Hide #HLK #HV1 #HVT #HI
    lapply (drop_fwd_drop2 … HLK) #H
    elim (cpy_inv_lift1_ge_up … HT2 … H … HVT) -HT2 -H -HVT
    [2,3,4: /2 width=1 by ylt_fwd_le_succ, yle_succ_dx/ ]
    /4 width=11 by cpys_strap1, ex6_5_intro, or_intror/
  ]
]
qed-.

lemma cpys_inv_lref1: ∀G,L,T2,i,d,e. ⦃G, L⦄ ⊢ #i ▶*[d, e] T2 →
                      T2 = #i ∨
                      ∃∃I,K,V1,V2. d ≤ i & i < d + e &
                                   ⇩[i] L ≡ K.ⓑ{I}V1 &
                                   ⦃G, K⦄ ⊢ V1 ▶*[0, ⫰(d+e-i)] V2 &
                                   ⇧[O, i+1] V2 ≡ T2.
#G #L #T2 #i #d #e #H elim (cpys_inv_atom1 … H) -H /2 width=1 by or_introl/
* #I #K #V1 #V2 #j #Hdj #Hjde #HLK #HV12 #HVT2 #H destruct /3 width=7 by ex5_4_intro, or_intror/
qed-.

lemma cpys_inv_lref1_Y2: ∀G,L,T2,i,d. ⦃G, L⦄ ⊢ #i ▶*[d, ∞] T2 →
                         T2 = #i ∨
                         ∃∃I,K,V1,V2. d ≤ i & ⇩[i] L ≡ K.ⓑ{I}V1 &
                                      ⦃G, K⦄ ⊢ V1 ▶*[0, ∞] V2 & ⇧[O, i+1] V2 ≡ T2.
#G #L #T2 #i #d #H elim (cpys_inv_lref1 … H) -H /2 width=1 by or_introl/
* >yminus_Y_inj /3 width=7 by or_intror, ex4_4_intro/
qed-.

lemma cpys_inv_lref1_drop: ∀G,L,T2,i,d,e. ⦃G, L⦄ ⊢ #i ▶*[d, e] T2 →
                            ∀I,K,V1. ⇩[i] L ≡ K.ⓑ{I}V1 →
                            ∀V2. ⇧[O, i+1] V2 ≡ T2 →
                            ∧∧ ⦃G, K⦄ ⊢ V1 ▶*[0, ⫰(d+e-i)] V2
                             & d ≤ i
                             & i < d + e.
#G #L #T2 #i #d #e #H #I #K #V1 #HLK #V2 #HVT2 elim (cpys_inv_lref1 … H) -H
[ #H destruct elim (lift_inv_lref2_be … HVT2) -HVT2 -HLK //
| * #Z #Y #X1 #X2 #Hdi #Hide #HLY #HX12 #HXT2
  lapply (lift_inj … HXT2 … HVT2) -T2 #H destruct
  lapply (drop_mono … HLY … HLK) -L #H destruct
  /2 width=1 by and3_intro/
]
qed-.

(* Properties on relocation *************************************************)

lemma cpys_lift_le: ∀G,K,T1,T2,dt,et. ⦃G, K⦄ ⊢ T1 ▶*[dt, et] T2 →
                    ∀L,U1,s,d,e. dt + et ≤ yinj d → ⇩[s, d, e] L ≡ K →
                    ⇧[d, e] T1 ≡ U1 → ∀U2. ⇧[d, e] T2 ≡ U2 →
                    ⦃G, L⦄ ⊢ U1 ▶*[dt, et] U2.
#G #K #T1 #T2 #dt #et #H #L #U1 #s #d #e #Hdetd #HLK #HTU1 @(cpys_ind … H) -T2
[ #U2 #H >(lift_mono … HTU1 … H) -H //
| -HTU1 #T #T2 #_ #HT2 #IHT #U2 #HTU2
  elim (lift_total T d e) #U #HTU
  lapply (IHT … HTU) -IHT #HU1
  lapply (cpy_lift_le … HT2 … HLK HTU HTU2 ?) -HT2 -HLK -HTU -HTU2 /2 width=3 by cpys_strap1/
]
qed-.

lemma cpys_lift_be: ∀G,K,T1,T2,dt,et. ⦃G, K⦄ ⊢ T1 ▶*[dt, et] T2 →
                    ∀L,U1,s,d,e. dt ≤ yinj d → d ≤ dt + et →
                    ⇩[s, d, e] L ≡ K → ⇧[d, e] T1 ≡ U1 →
                    ∀U2. ⇧[d, e] T2 ≡ U2 → ⦃G, L⦄ ⊢ U1 ▶*[dt, et + e] U2.
#G #K #T1 #T2 #dt #et #H #L #U1 #s #d #e #Hdtd #Hddet #HLK #HTU1 @(cpys_ind … H) -T2
[ #U2 #H >(lift_mono … HTU1 … H) -H //
| -HTU1 #T #T2 #_ #HT2 #IHT #U2 #HTU2
  elim (lift_total T d e) #U #HTU
  lapply (IHT … HTU) -IHT #HU1
  lapply (cpy_lift_be … HT2 … HLK HTU HTU2 ? ?) -HT2 -HLK -HTU -HTU2 /2 width=3 by cpys_strap1/
]
qed-.

lemma cpys_lift_ge: ∀G,K,T1,T2,dt,et. ⦃G, K⦄ ⊢ T1 ▶*[dt, et] T2 →
                    ∀L,U1,s,d,e. yinj d ≤ dt → ⇩[s, d, e] L ≡ K →
                    ⇧[d, e] T1 ≡ U1 → ∀U2. ⇧[d, e] T2 ≡ U2 →
                    ⦃G, L⦄ ⊢ U1 ▶*[dt+e, et] U2.
#G #K #T1 #T2 #dt #et #H #L #U1 #s #d #e #Hddt #HLK #HTU1 @(cpys_ind … H) -T2
[ #U2 #H >(lift_mono … HTU1 … H) -H //
| -HTU1 #T #T2 #_ #HT2 #IHT #U2 #HTU2
  elim (lift_total T d e) #U #HTU
  lapply (IHT … HTU) -IHT #HU1
  lapply (cpy_lift_ge … HT2 … HLK HTU HTU2 ?) -HT2 -HLK -HTU -HTU2 /2 width=3 by cpys_strap1/
]
qed-.

(* Inversion lemmas for relocation ******************************************)

lemma cpys_inv_lift1_le: ∀G,L,U1,U2,dt,et. ⦃G, L⦄ ⊢ U1 ▶*[dt, et] U2 →
                         ∀K,s,d,e. ⇩[s, d, e] L ≡ K → ∀T1. ⇧[d, e] T1 ≡ U1 →
                         dt + et ≤ d →
                         ∃∃T2. ⦃G, K⦄ ⊢ T1 ▶*[dt, et] T2 & ⇧[d, e] T2 ≡ U2.
#G #L #U1 #U2 #dt #et #H #K #s #d #e #HLK #T1 #HTU1 #Hdetd @(cpys_ind … H) -U2
[ /2 width=3 by ex2_intro/
| -HTU1 #U #U2 #_ #HU2 * #T #HT1 #HTU
  elim (cpy_inv_lift1_le … HU2 … HLK … HTU) -HU2 -HLK -HTU /3 width=3 by cpys_strap1, ex2_intro/
]
qed-.

lemma cpys_inv_lift1_be: ∀G,L,U1,U2,dt,et. ⦃G, L⦄ ⊢ U1 ▶*[dt, et] U2 →
                         ∀K,s,d,e. ⇩[s, d, e] L ≡ K → ∀T1. ⇧[d, e] T1 ≡ U1 →
                         dt ≤ d → yinj d + e ≤ dt + et →
                         ∃∃T2. ⦃G, K⦄ ⊢ T1 ▶*[dt, et - e] T2 & ⇧[d, e] T2 ≡ U2.
#G #L #U1 #U2 #dt #et #H #K #s #d #e #HLK #T1 #HTU1 #Hdtd #Hdedet @(cpys_ind … H) -U2
[ /2 width=3 by ex2_intro/
| -HTU1 #U #U2 #_ #HU2 * #T #HT1 #HTU
  elim (cpy_inv_lift1_be … HU2 … HLK … HTU) -HU2 -HLK -HTU /3 width=3 by cpys_strap1, ex2_intro/
]
qed-.

lemma cpys_inv_lift1_ge: ∀G,L,U1,U2,dt,et. ⦃G, L⦄ ⊢ U1 ▶*[dt, et] U2 →
                         ∀K,s,d,e. ⇩[s, d, e] L ≡ K → ∀T1. ⇧[d, e] T1 ≡ U1 →
                         yinj d + e ≤ dt →
                         ∃∃T2. ⦃G, K⦄ ⊢ T1 ▶*[dt - e, et] T2 & ⇧[d, e] T2 ≡ U2.
#G #L #U1 #U2 #dt #et #H #K #s #d #e #HLK #T1 #HTU1 #Hdedt @(cpys_ind … H) -U2
[ /2 width=3 by ex2_intro/
| -HTU1 #U #U2 #_ #HU2 * #T #HT1 #HTU
  elim (cpy_inv_lift1_ge … HU2 … HLK … HTU) -HU2 -HLK -HTU /3 width=3 by cpys_strap1, ex2_intro/
]
qed-.

(* Advanced inversion lemmas on relocation **********************************)

lemma cpys_inv_lift1_ge_up: ∀G,L,U1,U2,dt,et. ⦃G, L⦄ ⊢ U1 ▶*[dt, et] U2 →
                            ∀K,s,d,e. ⇩[s, d, e] L ≡ K → ∀T1. ⇧[d, e] T1 ≡ U1 →
                            d ≤ dt → dt ≤ yinj d + e → yinj d + e ≤ dt + et →
                            ∃∃T2. ⦃G, K⦄ ⊢ T1 ▶*[d, dt + et - (yinj d + e)] T2 &
                                 ⇧[d, e] T2 ≡ U2.
#G #L #U1 #U2 #dt #et #H #K #s #d #e #HLK #T1 #HTU1 #Hddt #Hdtde #Hdedet @(cpys_ind … H) -U2
[ /2 width=3 by ex2_intro/
| -HTU1 #U #U2 #_ #HU2 * #T #HT1 #HTU
  elim (cpy_inv_lift1_ge_up … HU2 … HLK … HTU) -HU2 -HLK -HTU /3 width=3 by cpys_strap1, ex2_intro/
]
qed-.

lemma cpys_inv_lift1_be_up: ∀G,L,U1,U2,dt,et. ⦃G, L⦄ ⊢ U1 ▶*[dt, et] U2 →
                            ∀K,s,d,e. ⇩[s, d, e] L ≡ K → ∀T1. ⇧[d, e] T1 ≡ U1 →
                            dt ≤ d → dt + et ≤ yinj d + e →
                            ∃∃T2. ⦃G, K⦄ ⊢ T1 ▶*[dt, d - dt] T2 & ⇧[d, e] T2 ≡ U2.
#G #L #U1 #U2 #dt #et #H #K #s #d #e #HLK #T1 #HTU1 #Hdtd #Hdetde @(cpys_ind … H) -U2
[ /2 width=3 by ex2_intro/
| -HTU1 #U #U2 #_ #HU2 * #T #HT1 #HTU
  elim (cpy_inv_lift1_be_up … HU2 … HLK … HTU) -HU2 -HLK -HTU /3 width=3 by cpys_strap1, ex2_intro/
]
qed-.

lemma cpys_inv_lift1_le_up: ∀G,L,U1,U2,dt,et. ⦃G, L⦄ ⊢ U1 ▶*[dt, et] U2 →
                            ∀K,s,d,e. ⇩[s, d, e] L ≡ K → ∀T1. ⇧[d, e] T1 ≡ U1 →
                            dt ≤ d → d ≤ dt + et → dt + et ≤ yinj d + e →
                            ∃∃T2. ⦃G, K⦄ ⊢ T1 ▶*[dt, d - dt] T2 & ⇧[d, e] T2 ≡ U2.
#G #L #U1 #U2 #dt #et #H #K #s #d #e #HLK #T1 #HTU1 #Hdtd #Hddet #Hdetde @(cpys_ind … H) -U2
[ /2 width=3 by ex2_intro/
| -HTU1 #U #U2 #_ #HU2 * #T #HT1 #HTU
  elim (cpy_inv_lift1_le_up … HU2 … HLK … HTU) -HU2 -HLK -HTU /3 width=3 by cpys_strap1, ex2_intro/
]
qed-.

lemma cpys_inv_lift1_subst: ∀G,L,W1,W2,d,e. ⦃G, L⦄ ⊢ W1 ▶*[d, e] W2 →
                            ∀K,V1,i. ⇩[i+1] L ≡ K → ⇧[O, i+1] V1 ≡ W1 → 
                            d ≤ yinj i → i < d + e →
                            ∃∃V2.  ⦃G, K⦄ ⊢ V1 ▶*[O, ⫰(d+e-i)] V2 & ⇧[O, i+1] V2 ≡ W2.
#G #L #W1 #W2 #d #e #HW12 #K #V1 #i #HLK #HVW1 #Hdi #Hide
elim (cpys_inv_lift1_ge_up … HW12 … HLK … HVW1 ? ? ?) //
>yplus_O1 <yplus_inj >yplus_SO2
[ >yminus_succ2 /2 width=3 by ex2_intro/
| /2 width=1 by ylt_fwd_le_succ1/
| /2 width=3 by yle_trans/
]
qed-.
