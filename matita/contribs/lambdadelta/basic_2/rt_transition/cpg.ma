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

include "ground_2/steps/rtc_max.ma".
include "ground_2/steps/rtc_plus.ma".
include "basic_2/notation/relations/predty_7.ma".
include "static_2/syntax/sh.ma".
include "static_2/syntax/lenv.ma".
include "static_2/syntax/genv.ma".
include "static_2/relocation/lifts.ma".

(* BOUND CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS *****************)

(* avtivate genv *)
inductive cpg (Rt:relation rtc) (h): rtc → relation4 genv lenv term term ≝
| cpg_atom : ∀I,G,L. cpg Rt h (𝟘𝟘) G L (⓪{I}) (⓪{I})
| cpg_ess  : ∀G,L,s. cpg Rt h (𝟘𝟙) G L (⋆s) (⋆(⫯[h]s))
| cpg_delta: ∀c,G,L,V1,V2,W2. cpg Rt h c G L V1 V2 →
             ⇧*[1] V2 ≘ W2 → cpg Rt h c G (L.ⓓV1) (#0) W2
| cpg_ell  : ∀c,G,L,V1,V2,W2. cpg Rt h c G L V1 V2 →
             ⇧*[1] V2 ≘ W2 → cpg Rt h (c+𝟘𝟙) G (L.ⓛV1) (#0) W2
| cpg_lref : ∀c,I,G,L,T,U,i. cpg Rt h c G L (#i) T →
             ⇧*[1] T ≘ U → cpg Rt h c G (L.ⓘ{I}) (#↑i) U
| cpg_bind : ∀cV,cT,p,I,G,L,V1,V2,T1,T2.
             cpg Rt h cV G L V1 V2 → cpg Rt h cT G (L.ⓑ{I}V1) T1 T2 →
             cpg Rt h ((↕*cV)∨cT) G L (ⓑ{p,I}V1.T1) (ⓑ{p,I}V2.T2)
| cpg_appl : ∀cV,cT,G,L,V1,V2,T1,T2.
             cpg Rt h cV G L V1 V2 → cpg Rt h cT G L T1 T2 →
             cpg Rt h ((↕*cV)∨cT) G L (ⓐV1.T1) (ⓐV2.T2)
| cpg_cast : ∀cU,cT,G,L,U1,U2,T1,T2. Rt cU cT →
             cpg Rt h cU G L U1 U2 → cpg Rt h cT G L T1 T2 →
             cpg Rt h (cU∨cT) G L (ⓝU1.T1) (ⓝU2.T2)
| cpg_zeta : ∀c,G,L,V,T1,T,T2. ⇧*[1] T ≘ T1 → cpg Rt h c G L T T2 →
             cpg Rt h (c+𝟙𝟘) G L (+ⓓV.T1) T2
| cpg_eps  : ∀c,G,L,V,T1,T2. cpg Rt h c G L T1 T2 → cpg Rt h (c+𝟙𝟘) G L (ⓝV.T1) T2
| cpg_ee   : ∀c,G,L,V1,V2,T. cpg Rt h c G L V1 V2 → cpg Rt h (c+𝟘𝟙) G L (ⓝV1.T) V2
| cpg_beta : ∀cV,cW,cT,p,G,L,V1,V2,W1,W2,T1,T2.
             cpg Rt h cV G L V1 V2 → cpg Rt h cW G L W1 W2 → cpg Rt h cT G (L.ⓛW1) T1 T2 →
             cpg Rt h (((↕*cV)∨(↕*cW)∨cT)+𝟙𝟘) G L (ⓐV1.ⓛ{p}W1.T1) (ⓓ{p}ⓝW2.V2.T2)
| cpg_theta: ∀cV,cW,cT,p,G,L,V1,V,V2,W1,W2,T1,T2.
             cpg Rt h cV G L V1 V → ⇧*[1] V ≘ V2 → cpg Rt h cW G L W1 W2 →
             cpg Rt h cT G (L.ⓓW1) T1 T2 →
             cpg Rt h (((↕*cV)∨(↕*cW)∨cT)+𝟙𝟘) G L (ⓐV1.ⓓ{p}W1.T1) (ⓓ{p}W2.ⓐV2.T2)
.

interpretation
   "bound context-sensitive parallel rt-transition (term)"
   'PRedTy Rt c h G L T1 T2 = (cpg Rt h c G L T1 T2).

(* Basic properties *********************************************************)

(* Note: this is "∀Rt. reflexive … Rt → ∀h,g,L. reflexive … (cpg Rt h (𝟘𝟘) L)" *)
lemma cpg_refl: ∀Rt. reflexive … Rt → ∀h,G,T,L. ⦃G,L⦄ ⊢ T ⬈[Rt,𝟘𝟘,h] T.
#Rt #HRt #h #G #T elim T -T // * /2 width=1 by cpg_bind/
* /2 width=1 by cpg_appl, cpg_cast/
qed.

(* Basic inversion lemmas ***************************************************)

fact cpg_inv_atom1_aux: ∀Rt,c,h,G,L,T1,T2. ⦃G,L⦄ ⊢ T1 ⬈[Rt,c,h] T2 → ∀J. T1 = ⓪{J} →
                        ∨∨ T2 = ⓪{J} ∧ c = 𝟘𝟘
                         | ∃∃s. J = Sort s & T2 = ⋆(⫯[h]s) & c = 𝟘𝟙
                         | ∃∃cV,K,V1,V2. ⦃G,K⦄ ⊢ V1 ⬈[Rt,cV,h] V2 & ⇧*[1] V2 ≘ T2 &
                                         L = K.ⓓV1 & J = LRef 0 & c = cV
                         | ∃∃cV,K,V1,V2. ⦃G,K⦄ ⊢ V1 ⬈[Rt,cV,h] V2 & ⇧*[1] V2 ≘ T2 &
                                         L = K.ⓛV1 & J = LRef 0 & c = cV+𝟘𝟙
                         | ∃∃I,K,T,i. ⦃G,K⦄ ⊢ #i ⬈[Rt,c,h] T & ⇧*[1] T ≘ T2 &
                                      L = K.ⓘ{I} & J = LRef (↑i).
#Rt #c #h #G #L #T1 #T2 * -c -G -L -T1 -T2
[ #I #G #L #J #H destruct /3 width=1 by or5_intro0, conj/
| #G #L #s #J #H destruct /3 width=3 by or5_intro1, ex3_intro/
| #c #G #L #V1 #V2 #W2 #HV12 #VW2 #J #H destruct /3 width=8 by or5_intro2, ex5_4_intro/
| #c #G #L #V1 #V2 #W2 #HV12 #VW2 #J #H destruct /3 width=8 by or5_intro3, ex5_4_intro/
| #c #I #G #L #T #U #i #HT #HTU #J #H destruct /3 width=8 by or5_intro4, ex4_4_intro/
| #cV #cT #p #I #G #L #V1 #V2 #T1 #T2 #_ #_ #J #H destruct
| #cV #cT #G #L #V1 #V2 #T1 #T2 #_ #_ #J #H destruct
| #cU #cT #G #L #U1 #U2 #T1 #T2 #_ #_ #_ #J #H destruct
| #c #G #L #V #T1 #T #T2 #_ #_ #J #H destruct
| #c #G #L #V #T1 #T2 #_ #J #H destruct
| #c #G #L #V1 #V2 #T #_ #J #H destruct
| #cV #cW #cT #p #G #L #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #J #H destruct
| #cV #cW #cT #p #G #L #V1 #V #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #J #H destruct
]
qed-.

lemma cpg_inv_atom1: ∀Rt,c,h,J,G,L,T2. ⦃G,L⦄ ⊢ ⓪{J} ⬈[Rt,c,h] T2 →
                     ∨∨ T2 = ⓪{J} ∧ c = 𝟘𝟘
                      | ∃∃s. J = Sort s & T2 = ⋆(⫯[h]s) & c = 𝟘𝟙
                      | ∃∃cV,K,V1,V2. ⦃G,K⦄ ⊢ V1 ⬈[Rt,cV,h] V2 & ⇧*[1] V2 ≘ T2 &
                                      L = K.ⓓV1 & J = LRef 0 & c = cV
                      | ∃∃cV,K,V1,V2. ⦃G,K⦄ ⊢ V1 ⬈[Rt,cV,h] V2 & ⇧*[1] V2 ≘ T2 &
                                      L = K.ⓛV1 & J = LRef 0 & c = cV+𝟘𝟙
                      | ∃∃I,K,T,i. ⦃G,K⦄ ⊢ #i ⬈[Rt,c,h] T & ⇧*[1] T ≘ T2 &
                                   L = K.ⓘ{I} & J = LRef (↑i).
/2 width=3 by cpg_inv_atom1_aux/ qed-.

lemma cpg_inv_sort1: ∀Rt,c,h,G,L,T2,s. ⦃G,L⦄ ⊢ ⋆s ⬈[Rt,c,h] T2 →
                     ∨∨ T2 = ⋆s ∧ c = 𝟘𝟘 | T2 = ⋆(⫯[h]s) ∧ c = 𝟘𝟙.
#Rt #c #h #G #L #T2 #s #H
elim (cpg_inv_atom1 … H) -H * /3 width=1 by or_introl, conj/
[ #s0 #H destruct /3 width=1 by or_intror, conj/
|2,3: #cV #K #V1 #V2 #_ #_ #_ #H destruct
| #I #K #T #i #_ #_ #_ #H destruct
]
qed-.

lemma cpg_inv_zero1: ∀Rt,c,h,G,L,T2. ⦃G,L⦄ ⊢ #0 ⬈[Rt,c,h] T2 →
                     ∨∨ T2 = #0 ∧ c = 𝟘𝟘
                      | ∃∃cV,K,V1,V2. ⦃G,K⦄ ⊢ V1 ⬈[Rt,cV,h] V2 & ⇧*[1] V2 ≘ T2 &
                                      L = K.ⓓV1 & c = cV
                      | ∃∃cV,K,V1,V2. ⦃G,K⦄ ⊢ V1 ⬈[Rt,cV,h] V2 & ⇧*[1] V2 ≘ T2 &
                                      L = K.ⓛV1 & c = cV+𝟘𝟙.
#Rt #c #h #G #L #T2 #H
elim (cpg_inv_atom1 … H) -H * /3 width=1 by or3_intro0, conj/
[ #s #H destruct
|2,3: #cV #K #V1 #V2 #HV12 #HVT2 #H1 #_ #H2 destruct /3 width=8 by or3_intro1, or3_intro2, ex4_4_intro/
| #I #K #T #i #_ #_ #_ #H destruct
]
qed-.

lemma cpg_inv_lref1: ∀Rt,c,h,G,L,T2,i. ⦃G,L⦄ ⊢ #↑i ⬈[Rt,c,h] T2 →
                     ∨∨ T2 = #(↑i) ∧ c = 𝟘𝟘
                      | ∃∃I,K,T. ⦃G,K⦄ ⊢ #i ⬈[Rt,c,h] T & ⇧*[1] T ≘ T2 & L = K.ⓘ{I}.
#Rt #c #h #G #L #T2 #i #H
elim (cpg_inv_atom1 … H) -H * /3 width=1 by or_introl, conj/
[ #s #H destruct
|2,3: #cV #K #V1 #V2 #_ #_ #_ #H destruct
| #I #K #T #j #HT #HT2 #H1 #H2 destruct /3 width=6 by ex3_3_intro, or_intror/
]
qed-.

lemma cpg_inv_gref1: ∀Rt,c,h,G,L,T2,l. ⦃G,L⦄ ⊢ §l ⬈[Rt,c,h] T2 → T2 = §l ∧ c = 𝟘𝟘.
#Rt #c #h #G #L #T2 #l #H
elim (cpg_inv_atom1 … H) -H * /2 width=1 by conj/
[ #s #H destruct
|2,3: #cV #K #V1 #V2 #_ #_ #_ #H destruct
| #I #K #T #i #_ #_ #_ #H destruct
]
qed-.

fact cpg_inv_bind1_aux: ∀Rt,c,h,G,L,U,U2. ⦃G,L⦄ ⊢ U ⬈[Rt,c,h] U2 →
                        ∀p,J,V1,U1. U = ⓑ{p,J}V1.U1 →
                        ∨∨ ∃∃cV,cT,V2,T2. ⦃G,L⦄ ⊢ V1 ⬈[Rt,cV,h] V2 & ⦃G,L.ⓑ{J}V1⦄ ⊢ U1 ⬈[Rt,cT,h] T2 &
                                          U2 = ⓑ{p,J}V2.T2 & c = ((↕*cV)∨cT)
                         | ∃∃cT,T. ⇧*[1] T ≘ U1 & ⦃G,L⦄ ⊢ T ⬈[Rt,cT,h] U2 &
                                   p = true & J = Abbr & c = cT+𝟙𝟘.
#Rt #c #h #G #L #U #U2 * -c -G -L -U -U2
[ #I #G #L #q #J #W #U1 #H destruct
| #G #L #s #q #J #W #U1 #H destruct
| #c #G #L #V1 #V2 #W2 #_ #_ #q #J #W #U1 #H destruct
| #c #G #L #V1 #V2 #W2 #_ #_ #q #J #W #U1 #H destruct
| #c #I #G #L #T #U #i #_ #_ #q #J #W #U1 #H destruct
| #cV #cT #p #I #G #L #V1 #V2 #T1 #T2 #HV12 #HT12 #q #J #W #U1 #H destruct /3 width=8 by ex4_4_intro, or_introl/
| #cV #cT #G #L #V1 #V2 #T1 #T2 #_ #_ #q #J #W #U1 #H destruct
| #cU #cT #G #L #U1 #U2 #T1 #T2 #_ #_ #_ #q #J #W #U1 #H destruct
| #c #G #L #V #T1 #T #T2 #HT1 #HT2 #q #J #W #U1 #H destruct /3 width=5 by ex5_2_intro, or_intror/
| #c #G #L #V #T1 #T2 #_ #q #J #W #U1 #H destruct
| #c #G #L #V1 #V2 #T #_ #q #J #W #U1 #H destruct
| #cV #cW #cT #p #G #L #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #q #J #W #U1 #H destruct
| #cV #cW #cT #p #G #L #V1 #V #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #q #J #W #U1 #H destruct
]
qed-.

lemma cpg_inv_bind1: ∀Rt,c,h,p,I,G,L,V1,T1,U2. ⦃G,L⦄ ⊢ ⓑ{p,I}V1.T1 ⬈[Rt,c,h] U2 →
                     ∨∨ ∃∃cV,cT,V2,T2. ⦃G,L⦄ ⊢ V1 ⬈[Rt,cV,h] V2 & ⦃G,L.ⓑ{I}V1⦄ ⊢ T1 ⬈[Rt,cT,h] T2 &
                                       U2 = ⓑ{p,I}V2.T2 & c = ((↕*cV)∨cT)
                      | ∃∃cT,T. ⇧*[1] T ≘ T1 & ⦃G,L⦄ ⊢ T ⬈[Rt,cT,h] U2 &
                                p = true & I = Abbr & c = cT+𝟙𝟘.
/2 width=3 by cpg_inv_bind1_aux/ qed-.

lemma cpg_inv_abbr1: ∀Rt,c,h,p,G,L,V1,T1,U2. ⦃G,L⦄ ⊢ ⓓ{p}V1.T1 ⬈[Rt,c,h] U2 →
                     ∨∨ ∃∃cV,cT,V2,T2. ⦃G,L⦄ ⊢ V1 ⬈[Rt,cV,h] V2 & ⦃G,L.ⓓV1⦄ ⊢ T1 ⬈[Rt,cT,h] T2 &
                                       U2 = ⓓ{p}V2.T2 & c = ((↕*cV)∨cT)
                      | ∃∃cT,T. ⇧*[1] T ≘ T1 & ⦃G,L⦄ ⊢ T ⬈[Rt,cT,h] U2 &
                                p = true & c = cT+𝟙𝟘.
#Rt #c #h #p #G #L #V1 #T1 #U2 #H elim (cpg_inv_bind1 … H) -H *
/3 width=8 by ex4_4_intro, ex4_2_intro, or_introl, or_intror/
qed-.

lemma cpg_inv_abst1: ∀Rt,c,h,p,G,L,V1,T1,U2. ⦃G,L⦄ ⊢ ⓛ{p}V1.T1 ⬈[Rt,c,h] U2 →
                     ∃∃cV,cT,V2,T2. ⦃G,L⦄ ⊢ V1 ⬈[Rt,cV,h] V2 & ⦃G,L.ⓛV1⦄ ⊢ T1 ⬈[Rt,cT,h] T2 &
                                    U2 = ⓛ{p}V2.T2 & c = ((↕*cV)∨cT).
#Rt #c #h #p #G #L #V1 #T1 #U2 #H elim (cpg_inv_bind1 … H) -H *
[ /3 width=8 by ex4_4_intro/
| #c #T #_ #_ #_ #H destruct
]
qed-.

fact cpg_inv_appl1_aux: ∀Rt,c,h,G,L,U,U2. ⦃G,L⦄ ⊢ U ⬈[Rt,c,h] U2 →
                        ∀V1,U1. U = ⓐV1.U1 →
                        ∨∨ ∃∃cV,cT,V2,T2. ⦃G,L⦄ ⊢ V1 ⬈[Rt,cV,h] V2 & ⦃G,L⦄ ⊢ U1 ⬈[Rt,cT,h] T2 &
                                          U2 = ⓐV2.T2 & c = ((↕*cV)∨cT)
                         | ∃∃cV,cW,cT,p,V2,W1,W2,T1,T2. ⦃G,L⦄ ⊢ V1 ⬈[Rt,cV,h] V2 & ⦃G,L⦄ ⊢ W1 ⬈[Rt,cW,h] W2 & ⦃G,L.ⓛW1⦄ ⊢ T1 ⬈[Rt,cT,h] T2 &
                                                        U1 = ⓛ{p}W1.T1 & U2 = ⓓ{p}ⓝW2.V2.T2 & c = ((↕*cV)∨(↕*cW)∨cT)+𝟙𝟘
                         | ∃∃cV,cW,cT,p,V,V2,W1,W2,T1,T2. ⦃G,L⦄ ⊢ V1 ⬈[Rt,cV,h] V & ⇧*[1] V ≘ V2 & ⦃G,L⦄ ⊢ W1 ⬈[Rt,cW,h] W2 & ⦃G,L.ⓓW1⦄ ⊢ T1 ⬈[Rt,cT,h] T2 &
                                                          U1 = ⓓ{p}W1.T1 & U2 = ⓓ{p}W2.ⓐV2.T2 & c = ((↕*cV)∨(↕*cW)∨cT)+𝟙𝟘.
#Rt #c #h #G #L #U #U2 * -c -G -L -U -U2
[ #I #G #L #W #U1 #H destruct
| #G #L #s #W #U1 #H destruct
| #c #G #L #V1 #V2 #W2 #_ #_ #W #U1 #H destruct
| #c #G #L #V1 #V2 #W2 #_ #_ #W #U1 #H destruct
| #c #I #G #L #T #U #i #_ #_ #W #U1 #H destruct
| #cV #cT #p #I #G #L #V1 #V2 #T1 #T2 #_ #_ #W #U1 #H destruct
| #cV #cT #G #L #V1 #V2 #T1 #T2 #HV12 #HT12 #W #U1 #H destruct /3 width=8 by or3_intro0, ex4_4_intro/
| #cV #cT #G #L #V1 #V2 #T1 #T2 #_ #_ #_ #W #U1 #H destruct
| #c #G #L #V #T1 #T #T2 #_ #_ #W #U1 #H destruct
| #c #G #L #V #T1 #T2 #_ #W #U1 #H destruct
| #c #G #L #V1 #V2 #T #_ #W #U1 #H destruct
| #cV #cW #cT #p #G #L #V1 #V2 #W1 #W2 #T1 #T2 #HV12 #HW12 #HT12 #W #U1 #H destruct /3 width=15 by or3_intro1, ex6_9_intro/
| #cV #cW #cT #p #G #L #V1 #V #V2 #W1 #W2 #T1 #T2 #HV1 #HV2 #HW12 #HT12 #W #U1 #H destruct /3 width=17 by or3_intro2, ex7_10_intro/
]
qed-.

lemma cpg_inv_appl1: ∀Rt,c,h,G,L,V1,U1,U2. ⦃G,L⦄ ⊢ ⓐV1.U1 ⬈[Rt,c,h] U2 →
                     ∨∨ ∃∃cV,cT,V2,T2. ⦃G,L⦄ ⊢ V1 ⬈[Rt,cV,h] V2 & ⦃G,L⦄ ⊢ U1 ⬈[Rt,cT,h] T2 &
                                       U2 = ⓐV2.T2 & c = ((↕*cV)∨cT)
                      | ∃∃cV,cW,cT,p,V2,W1,W2,T1,T2. ⦃G,L⦄ ⊢ V1 ⬈[Rt,cV,h] V2 & ⦃G,L⦄ ⊢ W1 ⬈[Rt,cW,h] W2 & ⦃G,L.ⓛW1⦄ ⊢ T1 ⬈[Rt,cT,h] T2 &
                                                     U1 = ⓛ{p}W1.T1 & U2 = ⓓ{p}ⓝW2.V2.T2 & c = ((↕*cV)∨(↕*cW)∨cT)+𝟙𝟘
                      | ∃∃cV,cW,cT,p,V,V2,W1,W2,T1,T2. ⦃G,L⦄ ⊢ V1 ⬈[Rt,cV,h] V & ⇧*[1] V ≘ V2 & ⦃G,L⦄ ⊢ W1 ⬈[Rt,cW,h] W2 & ⦃G,L.ⓓW1⦄ ⊢ T1 ⬈[Rt,cT,h] T2 &
                                                       U1 = ⓓ{p}W1.T1 & U2 = ⓓ{p}W2.ⓐV2.T2 & c = ((↕*cV)∨(↕*cW)∨cT)+𝟙𝟘.
/2 width=3 by cpg_inv_appl1_aux/ qed-.

fact cpg_inv_cast1_aux: ∀Rt,c,h,G,L,U,U2. ⦃G,L⦄ ⊢ U ⬈[Rt,c,h] U2 →
                        ∀V1,U1. U = ⓝV1.U1 →
                        ∨∨ ∃∃cV,cT,V2,T2. ⦃G,L⦄ ⊢ V1 ⬈[Rt,cV,h] V2 & ⦃G,L⦄ ⊢ U1 ⬈[Rt,cT,h] T2 &
                                          Rt cV cT & U2 = ⓝV2.T2 & c = (cV∨cT)
                         | ∃∃cT. ⦃G,L⦄ ⊢ U1 ⬈[Rt,cT,h] U2 & c = cT+𝟙𝟘
                         | ∃∃cV. ⦃G,L⦄ ⊢ V1 ⬈[Rt,cV,h] U2 & c = cV+𝟘𝟙.
#Rt #c #h #G #L #U #U2 * -c -G -L -U -U2
[ #I #G #L #W #U1 #H destruct
| #G #L #s #W #U1 #H destruct
| #c #G #L #V1 #V2 #W2 #_ #_ #W #U1 #H destruct
| #c #G #L #V1 #V2 #W2 #_ #_ #W #U1 #H destruct
| #c #I #G #L #T #U #i #_ #_ #W #U1 #H destruct
| #cV #cT #p #I #G #L #V1 #V2 #T1 #T2 #_ #_ #W #U1 #H destruct
| #cV #cT #G #L #V1 #V2 #T1 #T2 #_ #_ #W #U1 #H destruct
| #cV #cT #G #L #V1 #V2 #T1 #T2 #HRt #HV12 #HT12 #W #U1 #H destruct /3 width=9 by or3_intro0, ex5_4_intro/
| #c #G #L #V #T1 #T #T2 #_ #_ #W #U1 #H destruct
| #c #G #L #V #T1 #T2 #HT12 #W #U1 #H destruct /3 width=3 by or3_intro1, ex2_intro/
| #c #G #L #V1 #V2 #T #HV12 #W #U1 #H destruct /3 width=3 by or3_intro2, ex2_intro/
| #cV #cW #cT #p #G #L #V1 #V2 #W1 #W2 #T1 #T2 #HV12 #HW12 #HT12 #W #U1 #H destruct
| #cV #cW #cT #p #G #L #V1 #V #V2 #W1 #W2 #T1 #T2 #HV1 #HV2 #HW12 #HT12 #W #U1 #H destruct
]
qed-.

lemma cpg_inv_cast1: ∀Rt,c,h,G,L,V1,U1,U2. ⦃G,L⦄ ⊢ ⓝV1.U1 ⬈[Rt,c,h] U2 →
                     ∨∨ ∃∃cV,cT,V2,T2. ⦃G,L⦄ ⊢ V1 ⬈[Rt,cV,h] V2 & ⦃G,L⦄ ⊢ U1 ⬈[Rt,cT,h] T2 &
                                       Rt cV cT & U2 = ⓝV2.T2 & c = (cV∨cT)
                      | ∃∃cT. ⦃G,L⦄ ⊢ U1 ⬈[Rt,cT,h] U2 & c = cT+𝟙𝟘
                      | ∃∃cV. ⦃G,L⦄ ⊢ V1 ⬈[Rt,cV,h] U2 & c = cV+𝟘𝟙.
/2 width=3 by cpg_inv_cast1_aux/ qed-.

(* Advanced inversion lemmas ************************************************)

lemma cpg_inv_zero1_pair: ∀Rt,c,h,I,G,K,V1,T2. ⦃G,K.ⓑ{I}V1⦄ ⊢ #0 ⬈[Rt,c,h] T2 →
                          ∨∨ T2 = #0 ∧ c = 𝟘𝟘
                           | ∃∃cV,V2. ⦃G,K⦄ ⊢ V1 ⬈[Rt,cV,h] V2 & ⇧*[1] V2 ≘ T2 &
                                      I = Abbr & c = cV
                           | ∃∃cV,V2. ⦃G,K⦄ ⊢ V1 ⬈[Rt,cV,h] V2 & ⇧*[1] V2 ≘ T2 &
                                      I = Abst & c = cV+𝟘𝟙.
#Rt #c #h #I #G #K #V1 #T2 #H elim (cpg_inv_zero1 … H) -H /2 width=1 by or3_intro0/
* #z #Y #X1 #X2 #HX12 #HXT2 #H1 #H2 destruct /3 width=5 by or3_intro1, or3_intro2, ex4_2_intro/
qed-.

lemma cpg_inv_lref1_bind: ∀Rt,c,h,I,G,K,T2,i. ⦃G,K.ⓘ{I}⦄ ⊢ #↑i ⬈[Rt,c,h] T2 →
                          ∨∨ T2 = #(↑i) ∧ c = 𝟘𝟘
                           | ∃∃T. ⦃G,K⦄ ⊢ #i ⬈[Rt,c,h] T & ⇧*[1] T ≘ T2.
#Rt #c #h #I #G #L #T2 #i #H elim (cpg_inv_lref1 … H) -H /2 width=1 by or_introl/
* #Z #Y #T #HT #HT2 #H destruct /3 width=3 by ex2_intro, or_intror/
qed-.

(* Basic forward lemmas *****************************************************)

lemma cpg_fwd_bind1_minus: ∀Rt,c,h,I,G,L,V1,T1,T. ⦃G,L⦄ ⊢ -ⓑ{I}V1.T1 ⬈[Rt,c,h] T → ∀p.
                           ∃∃V2,T2. ⦃G,L⦄ ⊢ ⓑ{p,I}V1.T1 ⬈[Rt,c,h] ⓑ{p,I}V2.T2 &
                                    T = -ⓑ{I}V2.T2.
#Rt #c #h #I #G #L #V1 #T1 #T #H #p elim (cpg_inv_bind1 … H) -H *
[ #cV #cT #V2 #T2 #HV12 #HT12 #H1 #H2 destruct /3 width=4 by cpg_bind, ex2_2_intro/
| #c #T2 #_ #_ #H destruct
]
qed-.
