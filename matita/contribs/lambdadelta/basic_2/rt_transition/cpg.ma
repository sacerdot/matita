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

include "ground_2/steps/rtc_shift.ma".
include "ground_2/steps/rtc_plus.ma".
include "basic_2/notation/relations/predty_6.ma".
include "basic_2/grammar/lenv.ma".
include "basic_2/grammar/genv.ma".
include "basic_2/relocation/lifts.ma".
include "basic_2/static/sh.ma".

(* COUNTED CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS ***************)

(* avtivate genv *)
inductive cpg (h): rtc → relation4 genv lenv term term ≝
| cpg_atom : ∀I,G,L. cpg h (𝟘𝟘) G L (⓪{I}) (⓪{I})
| cpg_ess  : ∀G,L,s. cpg h (𝟘𝟙) G L (⋆s) (⋆(next h s))
| cpg_delta: ∀c,G,L,V1,V2,W2. cpg h c G L V1 V2 →
             ⬆*[1] V2 ≡ W2 → cpg h c G (L.ⓓV1) (#0) W2
| cpg_ell  : ∀c,G,L,V1,V2,W2. cpg h c G L V1 V2 →
             ⬆*[1] V2 ≡ W2 → cpg h ((↓c)+𝟘𝟙) G (L.ⓛV1) (#0) W2
| cpg_lref : ∀c,I,G,L,V,T,U,i. cpg h c G L (#i) T → 
             ⬆*[1] T ≡ U → cpg h c G (L.ⓑ{I}V) (#⫯i) U
| cpg_bind : ∀cV,cT,p,I,G,L,V1,V2,T1,T2.
             cpg h cV G L V1 V2 → cpg h cT G (L.ⓑ{I}V1) T1 T2 →
             cpg h ((↓cV)+cT) G L (ⓑ{p,I}V1.T1) (ⓑ{p,I}V2.T2)
| cpg_flat : ∀cV,cT,I,G,L,V1,V2,T1,T2.
             cpg h cV G L V1 V2 → cpg h cT G L T1 T2 →
             cpg h ((↓cV)+cT) G L (ⓕ{I}V1.T1) (ⓕ{I}V2.T2)
| cpg_zeta : ∀c,G,L,V,T1,T,T2. cpg h c G (L.ⓓV) T1 T →
             ⬆*[1] T2 ≡ T → cpg h ((↓c)+𝟙𝟘) G L (+ⓓV.T1) T2
| cpg_eps  : ∀c,G,L,V,T1,T2. cpg h c G L T1 T2 → cpg h ((↓c)+𝟙𝟘) G L (ⓝV.T1) T2
| cpg_ee   : ∀c,G,L,V1,V2,T. cpg h c G L V1 V2 → cpg h ((↓c)+𝟘𝟙) G L (ⓝV1.T) V2
| cpg_beta : ∀cV,cW,cT,p,G,L,V1,V2,W1,W2,T1,T2.
             cpg h cV G L V1 V2 → cpg h cW G L W1 W2 → cpg h cT G (L.ⓛW1) T1 T2 →
             cpg h ((↓cV)+(↓cW)+(↓cT)+𝟙𝟘) G L (ⓐV1.ⓛ{p}W1.T1) (ⓓ{p}ⓝW2.V2.T2)
| cpg_theta: ∀cV,cW,cT,p,G,L,V1,V,V2,W1,W2,T1,T2.
             cpg h cV G L V1 V → ⬆*[1] V ≡ V2 → cpg h cW G L W1 W2 →
             cpg h cT G (L.ⓓW1) T1 T2 →
             cpg h ((↓cV)+(↓cW)+(↓cT)+𝟙𝟘) G L (ⓐV1.ⓓ{p}W1.T1) (ⓓ{p}W2.ⓐV2.T2)
.

interpretation
   "counted context-sensitive parallel rt-transition (term)"
   'PRedTy c h G L T1 T2 = (cpg h c G L T1 T2).

(* Basic properties *********************************************************)

(* Note: this is "∀h,g,L. reflexive … (cpg h (𝟘𝟘) L)" *)
lemma cpg_refl: ∀h,G,T,L. ⦃G, L⦄ ⊢ T ⬈[𝟘𝟘, h] T.
#h #G #T elim T -T // * /2 width=1 by cpg_bind, cpg_flat/
qed.

lemma cpg_pair_sn: ∀c,h,I,G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ⬈[c, h] V2 →
                   ∀T. ⦃G, L⦄ ⊢ ②{I}V1.T ⬈[↓c, h] ②{I}V2.T.
#c #h * /2 width=1 by cpg_bind, cpg_flat/
qed.

(* Basic inversion lemmas ***************************************************)

fact cpg_inv_atom1_aux: ∀c,h,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ⬈[c, h] T2 → ∀J. T1 = ⓪{J} →
                        ∨∨ T2 = ⓪{J} ∧ c = 𝟘𝟘 
                         | ∃∃s. J = Sort s & T2 = ⋆(next h s) & c = 𝟘𝟙
                         | ∃∃cV,K,V1,V2. ⦃G, K⦄ ⊢ V1 ⬈[cV, h] V2 & ⬆*[1] V2 ≡ T2 &
                                         L = K.ⓓV1 & J = LRef 0 & c = cV
                         | ∃∃cV,K,V1,V2. ⦃G, K⦄ ⊢ V1 ⬈[cV, h] V2 & ⬆*[1] V2 ≡ T2 &
                                         L = K.ⓛV1 & J = LRef 0 & c = (↓cV)+𝟘𝟙
                         | ∃∃I,K,V,T,i. ⦃G, K⦄ ⊢ #i ⬈[c, h] T & ⬆*[1] T ≡ T2 &
                                        L = K.ⓑ{I}V & J = LRef (⫯i).
#c #h #G #L #T1 #T2 * -c -G -L -T1 -T2
[ #I #G #L #J #H destruct /3 width=1 by or5_intro0, conj/
| #G #L #s #J #H destruct /3 width=3 by or5_intro1, ex3_intro/
| #c #G #L #V1 #V2 #W2 #HV12 #VW2 #J #H destruct /3 width=8 by or5_intro2, ex5_4_intro/
| #c #G #L #V1 #V2 #W2 #HV12 #VW2 #J #H destruct /3 width=8 by or5_intro3, ex5_4_intro/
| #c #I #G #L #V #T #U #i #HT #HTU #J #H destruct /3 width=9 by or5_intro4, ex4_5_intro/
| #cV #cT #p #I #G #L #V1 #V2 #T1 #T2 #_ #_ #J #H destruct
| #cV #cT #I #G #L #V1 #V2 #T1 #T2 #_ #_ #J #H destruct
| #c #G #L #V #T1 #T #T2 #_ #_ #J #H destruct
| #c #G #L #V #T1 #T2 #_ #J #H destruct
| #c #G #L #V1 #V2 #T #_ #J #H destruct
| #cV #cW #cT #p #G #L #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #J #H destruct
| #cV #cW #cT #p #G #L #V1 #V #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #J #H destruct
]
qed-.

lemma cpg_inv_atom1: ∀c,h,J,G,L,T2. ⦃G, L⦄ ⊢ ⓪{J} ⬈[c, h] T2 →
                     ∨∨ T2 = ⓪{J} ∧ c = 𝟘𝟘 
                      | ∃∃s. J = Sort s & T2 = ⋆(next h s) & c = 𝟘𝟙
                      | ∃∃cV,K,V1,V2. ⦃G, K⦄ ⊢ V1 ⬈[cV, h] V2 & ⬆*[1] V2 ≡ T2 &
                                      L = K.ⓓV1 & J = LRef 0 & c = cV
                      | ∃∃cV,K,V1,V2. ⦃G, K⦄ ⊢ V1 ⬈[cV, h] V2 & ⬆*[1] V2 ≡ T2 &
                                      L = K.ⓛV1 & J = LRef 0 & c = (↓cV)+𝟘𝟙
                      | ∃∃I,K,V,T,i. ⦃G, K⦄ ⊢ #i ⬈[c, h] T & ⬆*[1] T ≡ T2 &
                                     L = K.ⓑ{I}V & J = LRef (⫯i).
/2 width=3 by cpg_inv_atom1_aux/ qed-.

lemma cpg_inv_sort1: ∀c,h,G,L,T2,s. ⦃G, L⦄ ⊢ ⋆s ⬈[c, h] T2 →
                     (T2 = ⋆s ∧ c = 𝟘𝟘) ∨ (T2 = ⋆(next h s) ∧ c = 𝟘𝟙).
#c #h #G #L #T2 #s #H
elim (cpg_inv_atom1 … H) -H * /3 width=1 by or_introl, conj/
[ #s0 #H destruct /3 width=1 by or_intror, conj/
|2,3: #cV #K #V1 #V2 #_ #_ #_ #H destruct
| #I #K #V1 #V2 #i #_ #_ #_ #H destruct
]
qed-.

lemma cpg_inv_zero1: ∀c,h,G,L,T2. ⦃G, L⦄ ⊢ #0 ⬈[c, h] T2 →
                     ∨∨ (T2 = #0 ∧ c = 𝟘𝟘)
                      | ∃∃cV,K,V1,V2. ⦃G, K⦄ ⊢ V1 ⬈[cV, h] V2 & ⬆*[1] V2 ≡ T2 &
                                      L = K.ⓓV1 & c = cV
                      | ∃∃cV,K,V1,V2. ⦃G, K⦄ ⊢ V1 ⬈[cV, h] V2 & ⬆*[1] V2 ≡ T2 &
                                      L = K.ⓛV1 & c = (↓cV)+𝟘𝟙.
#c #h #G #L #T2 #H
elim (cpg_inv_atom1 … H) -H * /3 width=1 by or3_intro0, conj/
[ #s #H destruct
|2,3: #cV #K #V1 #V2 #HV12 #HVT2 #H1 #_ #H2 destruct /3 width=8 by or3_intro1, or3_intro2, ex4_4_intro/
| #I #K #V1 #V2 #i #_ #_ #_ #H destruct
]
qed-.

lemma cpg_inv_lref1: ∀c,h,G,L,T2,i. ⦃G, L⦄ ⊢ #⫯i ⬈[c, h] T2 →
                     (T2 = #(⫯i) ∧ c = 𝟘𝟘) ∨
                     ∃∃I,K,V,T. ⦃G, K⦄ ⊢ #i ⬈[c, h] T & ⬆*[1] T ≡ T2 & L = K.ⓑ{I}V.
#c #h #G #L #T2 #i #H
elim (cpg_inv_atom1 … H) -H * /3 width=1 by or_introl, conj/
[ #s #H destruct
|2,3: #cV #K #V1 #V2 #_ #_ #_ #H destruct
| #I #K #V1 #V2 #j #HV2 #HVT2 #H1 #H2 destruct /3 width=7 by ex3_4_intro, or_intror/
]
qed-.

lemma cpg_inv_gref1: ∀c,h,G,L,T2,l. ⦃G, L⦄ ⊢ §l ⬈[c, h] T2 → T2 = §l ∧ c = 𝟘𝟘.
#c #h #G #L #T2 #l #H
elim (cpg_inv_atom1 … H) -H * /2 width=1 by conj/
[ #s #H destruct
|2,3: #cV #K #V1 #V2 #_ #_ #_ #H destruct
| #I #K #V1 #V2 #i #_ #_ #_ #H destruct
]
qed-.

fact cpg_inv_bind1_aux: ∀c,h,G,L,U,U2. ⦃G, L⦄ ⊢ U ⬈[c, h] U2 →
                        ∀p,J,V1,U1. U = ⓑ{p,J}V1.U1 → (
                        ∃∃cV,cT,V2,T2. ⦃G, L⦄ ⊢ V1 ⬈[cV, h] V2 & ⦃G, L.ⓑ{J}V1⦄ ⊢ U1 ⬈[cT, h] T2 &
                                       U2 = ⓑ{p,J}V2.T2 & c = (↓cV)+cT
                        ) ∨
                        ∃∃cT,T. ⦃G, L.ⓓV1⦄ ⊢ U1 ⬈[cT, h] T & ⬆*[1] U2 ≡ T &
                                p = true & J = Abbr & c = (↓cT)+𝟙𝟘.
#c #h #G #L #U #U2 * -c -G -L -U -U2
[ #I #G #L #q #J #W #U1 #H destruct
| #G #L #s #q #J #W #U1 #H destruct
| #c #G #L #V1 #V2 #W2 #_ #_ #q #J #W #U1 #H destruct
| #c #G #L #V1 #V2 #W2 #_ #_ #q #J #W #U1 #H destruct
| #c #I #G #L #V #T #U #i #_ #_ #q #J #W #U1 #H destruct
| #rv #cT #p #I #G #L #V1 #V2 #T1 #T2 #HV12 #HT12 #q #J #W #U1 #H destruct /3 width=8 by ex4_4_intro, or_introl/
| #rv #cT #I #G #L #V1 #V2 #T1 #T2 #_ #_ #q #J #W #U1 #H destruct
| #c #G #L #V #T1 #T #T2 #HT1 #HT2 #q #J #W #U1 #H destruct /3 width=5 by ex5_2_intro, or_intror/
| #c #G #L #V #T1 #T2 #_ #q #J #W #U1 #H destruct
| #c #G #L #V1 #V2 #T #_ #q #J #W #U1 #H destruct
| #rv #cW #cT #p #G #L #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #q #J #W #U1 #H destruct
| #rv #cW #cT #p #G #L #V1 #V #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #q #J #W #U1 #H destruct
]
qed-.

lemma cpg_inv_bind1: ∀c,h,p,I,G,L,V1,T1,U2. ⦃G, L⦄ ⊢ ⓑ{p,I}V1.T1 ⬈[c, h] U2 → (
                     ∃∃cV,cT,V2,T2. ⦃G, L⦄ ⊢ V1 ⬈[cV, h] V2 & ⦃G, L.ⓑ{I}V1⦄ ⊢ T1 ⬈[cT, h] T2 &
                                    U2 = ⓑ{p,I}V2.T2 & c = (↓cV)+cT
                     ) ∨
                     ∃∃cT,T. ⦃G, L.ⓓV1⦄ ⊢ T1 ⬈[cT, h] T & ⬆*[1] U2 ≡ T &
                             p = true & I = Abbr & c = (↓cT)+𝟙𝟘.
/2 width=3 by cpg_inv_bind1_aux/ qed-.

lemma cpg_inv_abbr1: ∀c,h,p,G,L,V1,T1,U2. ⦃G, L⦄ ⊢ ⓓ{p}V1.T1 ⬈[c, h] U2 → (
                     ∃∃cV,cT,V2,T2. ⦃G, L⦄ ⊢ V1 ⬈[cV, h] V2 & ⦃G, L.ⓓV1⦄ ⊢ T1 ⬈[cT, h] T2 &
                                    U2 = ⓓ{p}V2.T2 & c = (↓cV)+cT
                     ) ∨
                     ∃∃cT,T. ⦃G, L.ⓓV1⦄ ⊢ T1 ⬈[cT, h] T & ⬆*[1] U2 ≡ T &
                             p = true & c = (↓cT)+𝟙𝟘.
#c #h #p #G #L #V1 #T1 #U2 #H elim (cpg_inv_bind1 … H) -H *
/3 width=8 by ex4_4_intro, ex4_2_intro, or_introl, or_intror/
qed-.

lemma cpg_inv_abst1: ∀c,h,p,G,L,V1,T1,U2. ⦃G, L⦄ ⊢ ⓛ{p}V1.T1 ⬈[c, h] U2 →
                     ∃∃cV,cT,V2,T2. ⦃G, L⦄ ⊢ V1 ⬈[cV, h] V2 & ⦃G, L.ⓛV1⦄ ⊢ T1 ⬈[cT, h] T2 &
                                    U2 = ⓛ{p}V2.T2 & c = (↓cV)+cT.
#c #h #p #G #L #V1 #T1 #U2 #H elim (cpg_inv_bind1 … H) -H * 
[ /3 width=8 by ex4_4_intro/
| #c #T #_ #_ #_ #H destruct
]
qed-.

fact cpg_inv_flat1_aux: ∀c,h,G,L,U,U2. ⦃G, L⦄ ⊢ U ⬈[c, h] U2 →
                        ∀J,V1,U1. U = ⓕ{J}V1.U1 →
                        ∨∨ ∃∃cV,cT,V2,T2. ⦃G, L⦄ ⊢ V1 ⬈[cV, h] V2 & ⦃G, L⦄ ⊢ U1 ⬈[cT, h] T2 &
                                          U2 = ⓕ{J}V2.T2 & c = (↓cV)+cT
                         | ∃∃cT. ⦃G, L⦄ ⊢ U1 ⬈[cT, h] U2 & J = Cast & c = (↓cT)+𝟙𝟘
                         | ∃∃cV. ⦃G, L⦄ ⊢ V1 ⬈[cV, h] U2 & J = Cast & c = (↓cV)+𝟘𝟙
                         | ∃∃cV,cW,cT,p,V2,W1,W2,T1,T2. ⦃G, L⦄ ⊢ V1 ⬈[cV, h] V2 & ⦃G, L⦄ ⊢ W1 ⬈[cW, h] W2 & ⦃G, L.ⓛW1⦄ ⊢ T1 ⬈[cT, h] T2 &
                                                        J = Appl & U1 = ⓛ{p}W1.T1 & U2 = ⓓ{p}ⓝW2.V2.T2 & c = (↓cV)+(↓cW)+(↓cT)+𝟙𝟘
                         | ∃∃cV,cW,cT,p,V,V2,W1,W2,T1,T2. ⦃G, L⦄ ⊢ V1 ⬈[cV, h] V & ⬆*[1] V ≡ V2 & ⦃G, L⦄ ⊢ W1 ⬈[cW, h] W2 & ⦃G, L.ⓓW1⦄ ⊢ T1 ⬈[cT, h] T2 &
                                                          J = Appl & U1 = ⓓ{p}W1.T1 & U2 = ⓓ{p}W2.ⓐV2.T2 & c = (↓cV)+(↓cW)+(↓cT)+𝟙𝟘.
#c #h #G #L #U #U2 * -c -G -L -U -U2
[ #I #G #L #J #W #U1 #H destruct
| #G #L #s #J #W #U1 #H destruct
| #c #G #L #V1 #V2 #W2 #_ #_ #J #W #U1 #H destruct
| #c #G #L #V1 #V2 #W2 #_ #_ #J #W #U1 #H destruct
| #c #I #G #L #V #T #U #i #_ #_ #J #W #U1 #H destruct
| #rv #cT #p #I #G #L #V1 #V2 #T1 #T2 #_ #_ #J #W #U1 #H destruct
| #rv #cT #I #G #L #V1 #V2 #T1 #T2 #HV12 #HT12 #J #W #U1 #H destruct /3 width=8 by or5_intro0, ex4_4_intro/
| #c #G #L #V #T1 #T #T2 #_ #_ #J #W #U1 #H destruct
| #c #G #L #V #T1 #T2 #HT12 #J #W #U1 #H destruct /3 width=3 by or5_intro1, ex3_intro/
| #c #G #L #V1 #V2 #T #HV12 #J #W #U1 #H destruct /3 width=3 by or5_intro2, ex3_intro/
| #rv #cW #cT #p #G #L #V1 #V2 #W1 #W2 #T1 #T2 #HV12 #HW12 #HT12 #J #W #U1 #H destruct /3 width=15 by or5_intro3, ex7_9_intro/
| #rv #cW #cT #p #G #L #V1 #V #V2 #W1 #W2 #T1 #T2 #HV1 #HV2 #HW12 #HT12 #J #W #U1 #H destruct /3 width=17 by or5_intro4, ex8_10_intro/
]
qed-.

lemma cpg_inv_flat1: ∀c,h,I,G,L,V1,U1,U2. ⦃G, L⦄ ⊢ ⓕ{I}V1.U1 ⬈[c, h] U2 →
                     ∨∨ ∃∃cV,cT,V2,T2. ⦃G, L⦄ ⊢ V1 ⬈[cV, h] V2 & ⦃G, L⦄ ⊢ U1 ⬈[cT, h] T2 &
                                       U2 = ⓕ{I}V2.T2 & c = (↓cV)+cT
                      | ∃∃cT. ⦃G, L⦄ ⊢ U1 ⬈[cT, h] U2 & I = Cast & c = (↓cT)+𝟙𝟘
                      | ∃∃cV. ⦃G, L⦄ ⊢ V1 ⬈[cV, h] U2 & I = Cast & c = (↓cV)+𝟘𝟙
                      | ∃∃cV,cW,cT,p,V2,W1,W2,T1,T2. ⦃G, L⦄ ⊢ V1 ⬈[cV, h] V2 & ⦃G, L⦄ ⊢ W1 ⬈[cW, h] W2 & ⦃G, L.ⓛW1⦄ ⊢ T1 ⬈[cT, h] T2 &
                                                     I = Appl & U1 = ⓛ{p}W1.T1 & U2 = ⓓ{p}ⓝW2.V2.T2 & c = (↓cV)+(↓cW)+(↓cT)+𝟙𝟘
                      | ∃∃cV,cW,cT,p,V,V2,W1,W2,T1,T2. ⦃G, L⦄ ⊢ V1 ⬈[cV, h] V & ⬆*[1] V ≡ V2 & ⦃G, L⦄ ⊢ W1 ⬈[cW, h] W2 & ⦃G, L.ⓓW1⦄ ⊢ T1 ⬈[cT, h] T2 &
                                                       I = Appl & U1 = ⓓ{p}W1.T1 & U2 = ⓓ{p}W2.ⓐV2.T2 & c = (↓cV)+(↓cW)+(↓cT)+𝟙𝟘.
/2 width=3 by cpg_inv_flat1_aux/ qed-.

lemma cpg_inv_appl1: ∀c,h,G,L,V1,U1,U2. ⦃G, L⦄ ⊢ ⓐV1.U1 ⬈[c, h] U2 →
                     ∨∨ ∃∃cV,cT,V2,T2. ⦃G, L⦄ ⊢ V1 ⬈[cV, h] V2 & ⦃G, L⦄ ⊢ U1 ⬈[cT, h] T2 &
                                       U2 = ⓐV2.T2 & c = (↓cV)+cT
                      | ∃∃cV,cW,cT,p,V2,W1,W2,T1,T2. ⦃G, L⦄ ⊢ V1 ⬈[cV, h] V2 & ⦃G, L⦄ ⊢ W1 ⬈[cW, h] W2 & ⦃G, L.ⓛW1⦄ ⊢ T1 ⬈[cT, h] T2 &
                                                     U1 = ⓛ{p}W1.T1 & U2 = ⓓ{p}ⓝW2.V2.T2 & c = (↓cV)+(↓cW)+(↓cT)+𝟙𝟘
                      | ∃∃cV,cW,cT,p,V,V2,W1,W2,T1,T2. ⦃G, L⦄ ⊢ V1 ⬈[cV, h] V & ⬆*[1] V ≡ V2 & ⦃G, L⦄ ⊢ W1 ⬈[cW, h] W2 & ⦃G, L.ⓓW1⦄ ⊢ T1 ⬈[cT, h] T2 &
                                                       U1 = ⓓ{p}W1.T1 & U2 = ⓓ{p}W2.ⓐV2.T2 & c = (↓cV)+(↓cW)+(↓cT)+𝟙𝟘.
#c #h #G #L #V1 #U1 #U2 #H elim (cpg_inv_flat1 … H) -H *
[ /3 width=8 by or3_intro0, ex4_4_intro/
|2,3: #c #_ #H destruct
| /3 width=15 by or3_intro1, ex6_9_intro/
| /3 width=17 by or3_intro2, ex7_10_intro/
]
qed-.

lemma cpg_inv_cast1: ∀c,h,G,L,V1,U1,U2. ⦃G, L⦄ ⊢ ⓝV1.U1 ⬈[c, h] U2 →
                     ∨∨ ∃∃cV,cT,V2,T2. ⦃G, L⦄ ⊢ V1 ⬈[cV, h] V2 & ⦃G, L⦄ ⊢ U1 ⬈[cT, h] T2 &
                                       U2 = ⓝV2.T2 & c = (↓cV)+cT
                      | ∃∃cT. ⦃G, L⦄ ⊢ U1 ⬈[cT, h] U2 & c = (↓cT)+𝟙𝟘
                      | ∃∃cV. ⦃G, L⦄ ⊢ V1 ⬈[cV, h] U2 & c = (↓cV)+𝟘𝟙.
#c #h #G #L #V1 #U1 #U2 #H elim (cpg_inv_flat1 … H) -H *
[ /3 width=8 by or3_intro0, ex4_4_intro/
|2,3: /3 width=3 by or3_intro1, or3_intro2, ex2_intro/
| #rv #cW #cT #p #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #H destruct
| #rv #cW #cT #p #V #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #H destruct
]
qed-.

(* Basic forward lemmas *****************************************************)

lemma cpg_fwd_bind1_minus: ∀c,h,I,G,L,V1,T1,T. ⦃G, L⦄ ⊢ -ⓑ{I}V1.T1 ⬈[c, h] T → ∀p.
                           ∃∃V2,T2. ⦃G, L⦄ ⊢ ⓑ{p,I}V1.T1 ⬈[c, h] ⓑ{p,I}V2.T2 &
                                    T = -ⓑ{I}V2.T2.
#c #h #I #G #L #V1 #T1 #T #H #p elim (cpg_inv_bind1 … H) -H *
[ #cV #cT #V2 #T2 #HV12 #HT12 #H1 #H2 destruct /3 width=4 by cpg_bind, ex2_2_intro/
| #c #T2 #_ #_ #H destruct
]
qed-.
