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
include "basic_2/notation/relations/pred_6.ma".
include "basic_2/grammar/lenv.ma".
include "basic_2/grammar/genv.ma".
include "basic_2/relocation/lifts.ma".
include "basic_2/static/sh.ma".

(* CONTEXT-SENSITIVE GENERIC PARALLEL RT-TRANSITION FOR TERMS ***************)

(* avtivate genv *)
inductive cpg (h): rtc → relation4 genv lenv term term ≝
| cpg_atom : ∀I,G,L. cpg h (𝟘𝟘) G L (⓪{I}) (⓪{I})
| cpg_ess  : ∀G,L,s. cpg h (𝟘𝟙) G L (⋆s) (⋆(next h s))
| cpg_delta: ∀r,G,L,V1,V2,W2. cpg h r G L V1 V2 →
             ⬆*[1] V2 ≡ W2 → cpg h (↓r) G (L.ⓓV1) (#0) W2
| cpg_ell  : ∀r,G,L,V1,V2,W2. cpg h r G L V1 V2 →
             ⬆*[1] V2 ≡ W2 → cpg h ((↓r)+𝟘𝟙) G (L.ⓛV1) (#0) W2
| cpt_lref : ∀r,I,G,L,V,T,U,i. cpg h r G L (#i) T → 
             ⬆*[1] T ≡ U → cpg h r G (L.ⓑ{I}V) (#⫯i) U
| cpg_bind : ∀rV,rT,p,I,G,L,V1,V2,T1,T2.
             cpg h rV G L V1 V2 → cpg h rT G (L.ⓑ{I}V1) T1 T2 →
             cpg h ((↓rV)+rT) G L (ⓑ{p,I}V1.T1) (ⓑ{p,I}V2.T2)
| cpg_flat : ∀rV,rT,I,G,L,V1,V2,T1,T2.
             cpg h rV G L V1 V2 → cpg h rT G L T1 T2 →
             cpg h ((↓rV)+rT) G L (ⓕ{I}V1.T1) (ⓕ{I}V2.T2)
| cpg_zeta : ∀r,G,L,V,T1,T,T2. cpg h r G (L.ⓓV) T1 T →
             ⬆*[1] T2 ≡ T → cpg h ((↓r)+𝟙𝟘) G L (+ⓓV.T1) T2
| cpg_eps  : ∀r,G,L,V,T1,T2. cpg h r G L T1 T2 → cpg h ((↓r)+𝟙𝟘) G L (ⓝV.T1) T2
| cpg_ee   : ∀r,G,L,V1,V2,T. cpg h r G L V1 V2 → cpg h ((↓r)+𝟘𝟙) G L (ⓝV1.T) V2
| cpg_beta : ∀rV,rW,rT,p,G,L,V1,V2,W1,W2,T1,T2.
             cpg h rV G L V1 V2 → cpg h rW G L W1 W2 → cpg h rT G (L.ⓛW1) T1 T2 →
             cpg h ((↓rV)+(↓rW)+(↓rT)+𝟙𝟘) G L (ⓐV1.ⓛ{p}W1.T1) (ⓓ{p}ⓝW2.V2.T2)
| cpg_theta: ∀rV,rW,rT,p,G,L,V1,V,V2,W1,W2,T1,T2.
             cpg h rV G L V1 V → ⬆*[1] V ≡ V2 → cpg h rW G L W1 W2 →
             cpg h rT G (L.ⓓW1) T1 T2 →
             cpg h ((↓rV)+(↓rW)+(↓rT)+𝟙𝟘) G L (ⓐV1.ⓓ{p}W1.T1) (ⓓ{p}W2.ⓐV2.T2)
.

interpretation
   "context-sensitive generic parallel rt-transition (term)"
   'PRed h r G L T1 T2 = (cpg h r G L T1 T2).

(* Basic properties *********************************************************)

(* Note: this is "∀h,g,L. reflexive … (cpg h (𝟘𝟘) L)" *)
lemma cpg_refl: ∀h,G,T,L. ⦃G, L⦄ ⊢ T ➡[h, 𝟘𝟘] T.
#h #G #T elim T -T // * /2 width=1 by cpg_bind, cpg_flat/
qed.

lemma cpg_pair_sn: ∀h,r,I,G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ➡[h, r] V2 →
                   ∀T. ⦃G, L⦄ ⊢ ②{I}V1.T ➡[h, ↓r] ②{I}V2.T.
#h #r * /2 width=1 by cpg_bind, cpg_flat/
qed.

(* Basic inversion lemmas ***************************************************)

fact cpg_inv_atom1_aux: ∀h,r,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡[h, r] T2 → ∀J. T1 = ⓪{J} →
                        ∨∨ T2 = ⓪{J}
                         | ∃∃s. J = Sort s & T2 = ⋆(next h s)
                         | ∃∃rV,K,V1,V2. ⦃G, K⦄ ⊢ V1 ➡[h, rV] V2 & ⬆*[1] V2 ≡ T2 &
                                         L = K.ⓓV1 & J = LRef 0 & r = ↓rV
                         | ∃∃rV,K,V1,V2. ⦃G, K⦄ ⊢ V1 ➡[h, rV] V2 & ⬆*[1] V2 ≡ T2 &
                                         L = K.ⓛV1 & J = LRef 0 & r = (↓rV)+𝟘𝟙
                         | ∃∃I,K,V,T,i. ⦃G, K⦄ ⊢ #i ➡[h, r] T & ⬆*[1] T ≡ T2 &
                                        L = K.ⓑ{I}V & J = LRef (⫯i).
#h #r #G #L #T1 #T2 * -r -G -L -T1 -T2
[ #I #G #L #J #H destruct /2 width=1 by or5_intro0/
| #G #L #s #J #H destruct /3 width=3 by or5_intro1, ex2_intro/
| #r #G #L #V1 #V2 #W2 #HV12 #VW2 #J #H destruct /3 width=8 by or5_intro2, ex5_4_intro/
| #r #G #L #V1 #V2 #W2 #HV12 #VW2 #J #H destruct /3 width=8 by or5_intro3, ex5_4_intro/
| #r #I #G #L #V #T #U #i #HT #HTU #J #H destruct /3 width=9 by or5_intro4, ex4_5_intro/
| #rV #rT #p #I #G #L #V1 #V2 #T1 #T2 #_ #_ #J #H destruct
| #rV #rT #I #G #L #V1 #V2 #T1 #T2 #_ #_ #J #H destruct
| #r #G #L #V #T1 #T #T2 #_ #_ #J #H destruct
| #r #G #L #V #T1 #T2 #_ #J #H destruct
| #r #G #L #V1 #V2 #T #_ #J #H destruct
| #rV #rW #rT #p #G #L #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #J #H destruct
| #rV #rW #rT #p #G #L #V1 #V #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #J #H destruct
]
qed-.

lemma cpg_inv_atom1: ∀h,r,J,G,L,T2. ⦃G, L⦄ ⊢ ⓪{J} ➡[h, r] T2 →
                     ∨∨ T2 = ⓪{J}
                      | ∃∃s. J = Sort s & T2 = ⋆(next h s)
                      | ∃∃rV,K,V1,V2. ⦃G, K⦄ ⊢ V1 ➡[h, rV] V2 & ⬆*[1] V2 ≡ T2 &
                                      L = K.ⓓV1 & J = LRef 0 & r = ↓rV
                      | ∃∃rV,K,V1,V2. ⦃G, K⦄ ⊢ V1 ➡[h, rV] V2 & ⬆*[1] V2 ≡ T2 &
                                      L = K.ⓛV1 & J = LRef 0 & r = (↓rV)+𝟘𝟙
                      | ∃∃I,K,V,T,i. ⦃G, K⦄ ⊢ #i ➡[h, r] T & ⬆*[1] T ≡ T2 &
                                     L = K.ⓑ{I}V & J = LRef (⫯i).
/2 width=3 by cpg_inv_atom1_aux/ qed-.

lemma cpg_inv_sort1: ∀h,r,G,L,T2,s. ⦃G, L⦄ ⊢ ⋆s ➡[h, r] T2 →
                     T2 = ⋆s ∨ T2 = ⋆(next h s).
#h #r #G #L #T2 #s #H
elim (cpg_inv_atom1 … H) -H /2 width=1 by or_introl/ *
[ #s0 #H destruct /2 width=1 by or_intror/
|2,3: #rV #K #V1 #V2 #_ #_ #_ #H destruct
| #I #K #V1 #V2 #i #_ #_ #_ #H destruct
]
qed-.

lemma cpg_inv_zero1: ∀h,r,G,L,T2. ⦃G, L⦄ ⊢ #0 ➡[h, r] T2 →
                     ∨∨ T2 = #0 
                      | ∃∃rV,K,V1,V2. ⦃G, K⦄ ⊢ V1 ➡[h, rV] V2 & ⬆*[1] V2 ≡ T2 &
                                      L = K.ⓓV1 & r = ↓rV
                      | ∃∃rV,K,V1,V2. ⦃G, K⦄ ⊢ V1 ➡[h, rV] V2 & ⬆*[1] V2 ≡ T2 &
                                      L = K.ⓛV1 & r = (↓rV)+𝟘𝟙.
#h #r #G #L #T2 #H
elim (cpg_inv_atom1 … H) -H /2 width=1 by or3_intro0/ *
[ #s #H destruct
|2,3: #rV #K #V1 #V2 #HV12 #HVT2 #H1 #_ #H2 destruct /3 width=8 by or3_intro1, or3_intro2, ex4_4_intro/
| #I #K #V1 #V2 #i #_ #_ #_ #H destruct
]
qed-.

lemma cpg_inv_lref1: ∀h,r,G,L,T2,i. ⦃G, L⦄ ⊢ #⫯i ➡[h, r] T2 →
                     (T2 = #⫯i) ∨
                     ∃∃I,K,V,T. ⦃G, K⦄ ⊢ #i ➡[h, r] T & ⬆*[1] T ≡ T2 & L = K.ⓑ{I}V.
#h #r #G #L #T2 #i #H
elim (cpg_inv_atom1 … H) -H /2 width=1 by or_introl/ *
[ #s #H destruct
|2,3: #rV #K #V1 #V2 #_ #_ #_ #H destruct
| #I #K #V1 #V2 #j #HV2 #HVT2 #H1 #H2 destruct /3 width=7 by ex3_4_intro, or_intror/
]
qed-.

lemma cpg_inv_gref1: ∀h,r,G,L,T2,l.  ⦃G, L⦄ ⊢ §l ➡[h, r] T2 → T2 = §l.
#h #r #G #L #T2 #l #H
elim (cpg_inv_atom1 … H) -H // *
[ #s #H destruct
|2,3: #rV #K #V1 #V2 #_ #_ #_ #H destruct
| #I #K #V1 #V2 #i #_ #_ #_ #H destruct
]
qed-.

fact cpg_inv_bind1_aux: ∀h,r,G,L,U,U2. ⦃G, L⦄ ⊢ U ➡[h, r] U2 →
                        ∀p,J,V1,U1. U = ⓑ{p,J}V1.U1 → (
                        ∃∃rV,rT,V2,T2. ⦃G, L⦄ ⊢ V1 ➡[h, rV] V2 & ⦃G, L.ⓑ{J}V1⦄ ⊢ U1 ➡[h, rT] T2 &
                                       U2 = ⓑ{p,J}V2.T2 & r = (↓rV)+rT
                        ) ∨
                        ∃∃rT,T. ⦃G, L.ⓓV1⦄ ⊢ U1 ➡[h, rT] T & ⬆*[1] U2 ≡ T &
                                p = true & J = Abbr & r = (↓rT)+𝟙𝟘.
#h #r #G #L #U #U2 * -r -G -L -U -U2
[ #I #G #L #q #J #W #U1 #H destruct
| #G #L #s #q #J #W #U1 #H destruct
| #r #G #L #V1 #V2 #W2 #_ #_ #q #J #W #U1 #H destruct
| #r #G #L #V1 #V2 #W2 #_ #_ #q #J #W #U1 #H destruct
| #r #I #G #L #V #T #U #i #_ #_ #q #J #W #U1 #H destruct
| #rv #rT #p #I #G #L #V1 #V2 #T1 #T2 #HV12 #HT12 #q #J #W #U1 #H destruct /3 width=8 by ex4_4_intro, or_introl/
| #rv #rT #I #G #L #V1 #V2 #T1 #T2 #_ #_ #q #J #W #U1 #H destruct
| #r #G #L #V #T1 #T #T2 #HT1 #HT2 #q #J #W #U1 #H destruct /3 width=5 by ex5_2_intro, or_intror/
| #r #G #L #V #T1 #T2 #_ #q #J #W #U1 #H destruct
| #r #G #L #V1 #V2 #T #_ #q #J #W #U1 #H destruct
| #rv #rW #rT #p #G #L #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #q #J #W #U1 #H destruct
| #rv #rW #rT #p #G #L #V1 #V #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #q #J #W #U1 #H destruct
]
qed-.

lemma cpg_inv_bind1: ∀h,r,p,I,G,L,V1,T1,U2. ⦃G, L⦄ ⊢ ⓑ{p,I}V1.T1 ➡[h, r] U2 → (
                     ∃∃rV,rT,V2,T2. ⦃G, L⦄ ⊢ V1 ➡[h, rV] V2 & ⦃G, L.ⓑ{I}V1⦄ ⊢ T1 ➡[h, rT] T2 &
                                    U2 = ⓑ{p,I}V2.T2 & r = (↓rV)+rT
                     ) ∨
                     ∃∃rT,T. ⦃G, L.ⓓV1⦄ ⊢ T1 ➡[h, rT] T & ⬆*[1] U2 ≡ T &
                             p = true & I = Abbr & r = (↓rT)+𝟙𝟘.
/2 width=3 by cpg_inv_bind1_aux/ qed-.

lemma cpg_inv_abbr1: ∀h,r,p,G,L,V1,T1,U2. ⦃G, L⦄ ⊢ ⓓ{p}V1.T1 ➡[h, r] U2 → (
                     ∃∃rV,rT,V2,T2. ⦃G, L⦄ ⊢ V1 ➡[h, rV] V2 & ⦃G, L.ⓓV1⦄ ⊢ T1 ➡[h, rT] T2 &
                                    U2 = ⓓ{p}V2.T2 & r = (↓rV)+rT
                     ) ∨
                     ∃∃rT,T. ⦃G, L.ⓓV1⦄ ⊢ T1 ➡[h, rT] T & ⬆*[1] U2 ≡ T &
                             p = true & r = (↓rT)+𝟙𝟘.
#h #r #p #G #L #V1 #T1 #U2 #H elim (cpg_inv_bind1 … H) -H *
/3 width=8 by ex4_4_intro, ex4_2_intro, or_introl, or_intror/
qed-.

lemma cpg_inv_abst1: ∀h,r,p,G,L,V1,T1,U2.  ⦃G, L⦄ ⊢ ⓛ{p}V1.T1 ➡[h, r] U2 →
                     ∃∃rV,rT,V2,T2. ⦃G, L⦄ ⊢ V1 ➡[h, rV] V2 & ⦃G, L.ⓛV1⦄ ⊢ T1 ➡[h, rT] T2 &
                                    U2 = ⓛ{p} V2. T2 & r = (↓rV)+rT.
#h #r #p #G #L #V1 #T1 #U2 #H elim (cpg_inv_bind1 … H) -H * 
[ /3 width=8 by ex4_4_intro/
| #r #T #_ #_ #_ #H destruct
]
qed-.

fact cpg_inv_flat1_aux: ∀h,r,G,L,U,U2. ⦃G, L⦄ ⊢ U ➡[h, r] U2 →
                        ∀J,V1,U1. U = ⓕ{J}V1.U1 →
                        ∨∨ ∃∃rV,rT,V2,T2. ⦃G, L⦄ ⊢ V1 ➡[h, rV] V2 & ⦃G, L⦄ ⊢ U1 ➡[h, rT] T2 &
                                          U2 = ⓕ{J}V2.T2 & r = (↓rV)+rT
                         | ∃∃rT. ⦃G, L⦄ ⊢ U1 ➡[h, rT] U2 & J = Cast & r = (↓rT)+𝟙𝟘
                         | ∃∃rV. ⦃G, L⦄ ⊢ V1 ➡[h, rV] U2 & J = Cast & r = (↓rV)+𝟘𝟙
                         | ∃∃rV,rW,rT,p,V2,W1,W2,T1,T2. ⦃G, L⦄ ⊢ V1 ➡[h, rV] V2 & ⦃G, L⦄ ⊢ W1 ➡[h, rW] W2 & ⦃G, L.ⓛW1⦄ ⊢ T1 ➡[h, rT] T2 &
                                                        J = Appl & U1 = ⓛ{p}W1.T1 & U2 = ⓓ{p}ⓝW2.V2.T2 & r = (↓rV)+(↓rW)+(↓rT)+𝟙𝟘
                         | ∃∃rV,rW,rT,p,V,V2,W1,W2,T1,T2. ⦃G, L⦄ ⊢ V1 ➡[h, rV] V & ⬆*[1] V ≡ V2 & ⦃G, L⦄ ⊢ W1 ➡[h, rW] W2 & ⦃G, L.ⓓW1⦄ ⊢ T1 ➡[h, rT] T2 &
                                                          J = Appl & U1 = ⓓ{p}W1.T1 & U2 = ⓓ{p}W2.ⓐV2.T2 & r = (↓rV)+(↓rW)+(↓rT)+𝟙𝟘.
#h #r #G #L #U #U2 * -r -G -L -U -U2
[ #I #G #L #J #W #U1 #H destruct
| #G #L #s #J #W #U1 #H destruct
| #r #G #L #V1 #V2 #W2 #_ #_ #J #W #U1 #H destruct
| #r #G #L #V1 #V2 #W2 #_ #_ #J #W #U1 #H destruct
| #r #I #G #L #V #T #U #i #_ #_ #J #W #U1 #H destruct
| #rv #rT #p #I #G #L #V1 #V2 #T1 #T2 #_ #_ #J #W #U1 #H destruct
| #rv #rT #I #G #L #V1 #V2 #T1 #T2 #HV12 #HT12 #J #W #U1 #H destruct /3 width=8 by or5_intro0, ex4_4_intro/
| #r #G #L #V #T1 #T #T2 #_ #_ #J #W #U1 #H destruct
| #r #G #L #V #T1 #T2 #HT12 #J #W #U1 #H destruct /3 width=3 by or5_intro1, ex3_intro/
| #r #G #L #V1 #V2 #T #HV12 #J #W #U1 #H destruct /3 width=3 by or5_intro2, ex3_intro/
| #rv #rW #rT #p #G #L #V1 #V2 #W1 #W2 #T1 #T2 #HV12 #HW12 #HT12 #J #W #U1 #H destruct /3 width=15 by or5_intro3, ex7_9_intro/
| #rv #rW #rT #p #G #L #V1 #V #V2 #W1 #W2 #T1 #T2 #HV1 #HV2 #HW12 #HT12 #J #W #U1 #H destruct /3 width=17 by or5_intro4, ex8_10_intro/
]
qed-.

lemma cpg_inv_flat1: ∀h,r,I,G,L,V1,U1,U2. ⦃G, L⦄ ⊢ ⓕ{I}V1.U1 ➡[h, r] U2 →
                     ∨∨ ∃∃rV,rT,V2,T2. ⦃G, L⦄ ⊢ V1 ➡[h, rV] V2 & ⦃G, L⦄ ⊢ U1 ➡[h, rT] T2 &
                                       U2 = ⓕ{I}V2.T2 & r = (↓rV)+rT
                      | ∃∃rT. ⦃G, L⦄ ⊢ U1 ➡[h, rT] U2 & I = Cast & r = (↓rT)+𝟙𝟘
                      | ∃∃rV. ⦃G, L⦄ ⊢ V1 ➡[h, rV] U2 & I = Cast & r = (↓rV)+𝟘𝟙
                      | ∃∃rV,rW,rT,p,V2,W1,W2,T1,T2. ⦃G, L⦄ ⊢ V1 ➡[h, rV] V2 & ⦃G, L⦄ ⊢ W1 ➡[h, rW] W2 & ⦃G, L.ⓛW1⦄ ⊢ T1 ➡[h, rT] T2 &
                                                     I = Appl & U1 = ⓛ{p}W1.T1 & U2 = ⓓ{p}ⓝW2.V2.T2 & r = (↓rV)+(↓rW)+(↓rT)+𝟙𝟘
                      | ∃∃rV,rW,rT,p,V,V2,W1,W2,T1,T2. ⦃G, L⦄ ⊢ V1 ➡[h, rV] V & ⬆*[1] V ≡ V2 & ⦃G, L⦄ ⊢ W1 ➡[h, rW] W2 & ⦃G, L.ⓓW1⦄ ⊢ T1 ➡[h, rT] T2 &
                                                       I = Appl & U1 = ⓓ{p}W1.T1 & U2 = ⓓ{p}W2.ⓐV2.T2 & r = (↓rV)+(↓rW)+(↓rT)+𝟙𝟘.
/2 width=3 by cpg_inv_flat1_aux/ qed-.

lemma cpg_inv_appl1: ∀h,r,G,L,V1,U1,U2. ⦃G, L⦄ ⊢ ⓐV1.U1 ➡[h, r] U2 →
                     ∨∨ ∃∃rV,rT,V2,T2. ⦃G, L⦄ ⊢ V1 ➡[h, rV] V2 & ⦃G, L⦄ ⊢ U1 ➡[h, rT] T2 &
                                       U2 = ⓐV2.T2 & r = (↓rV)+rT
                      | ∃∃rV,rW,rT,p,V2,W1,W2,T1,T2. ⦃G, L⦄ ⊢ V1 ➡[h, rV] V2 & ⦃G, L⦄ ⊢ W1 ➡[h, rW] W2 & ⦃G, L.ⓛW1⦄ ⊢ T1 ➡[h, rT] T2 &
                                                     U1 = ⓛ{p}W1.T1 & U2 = ⓓ{p}ⓝW2.V2.T2 & r = (↓rV)+(↓rW)+(↓rT)+𝟙𝟘
                      | ∃∃rV,rW,rT,p,V,V2,W1,W2,T1,T2. ⦃G, L⦄ ⊢ V1 ➡[h, rV] V & ⬆*[1] V ≡ V2 & ⦃G, L⦄ ⊢ W1 ➡[h, rW] W2 & ⦃G, L.ⓓW1⦄ ⊢ T1 ➡[h, rT] T2 &
                                                       U1 = ⓓ{p}W1.T1 & U2 = ⓓ{p}W2.ⓐV2.T2 & r = (↓rV)+(↓rW)+(↓rT)+𝟙𝟘.
#h #r #G #L #V1 #U1 #U2 #H elim (cpg_inv_flat1 … H) -H *
[ /3 width=8 by or3_intro0, ex4_4_intro/
|2,3: #r #_ #H destruct
| /3 width=15 by or3_intro1, ex6_9_intro/
| /3 width=17 by or3_intro2, ex7_10_intro/
]
qed-.

lemma cpg_inv_cast1: ∀h,r,G,L,V1,U1,U2. ⦃G, L⦄ ⊢ ⓝV1.U1 ➡[h, r] U2 →
                     ∨∨ ∃∃rV,rT,V2,T2. ⦃G, L⦄ ⊢ V1 ➡[h, rV] V2 & ⦃G, L⦄ ⊢ U1 ➡[h, rT] T2 &
                                       U2 = ⓝV2.T2 & r = (↓rV)+rT
                      | ∃∃rT. ⦃G, L⦄ ⊢ U1 ➡[h, rT] U2 & r = (↓rT)+𝟙𝟘
                      | ∃∃rV. ⦃G, L⦄ ⊢ V1 ➡[h, rV] U2 & r = (↓rV)+𝟘𝟙.
#h #r #G #L #V1 #U1 #U2 #H elim (cpg_inv_flat1 … H) -H *
[ /3 width=8 by or3_intro0, ex4_4_intro/
|2,3: /3 width=3 by or3_intro1, or3_intro2, ex2_intro/
| #rv #rW #rT #p #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #H destruct
| #rv #rW #rT #p #V #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #H destruct
]
qed-.

(* Basic forward lemmas *****************************************************)

lemma cpg_fwd_bind1_minus: ∀h,r,I,G,L,V1,T1,T. ⦃G, L⦄ ⊢ -ⓑ{I}V1.T1 ➡[h, r] T → ∀b.
                           ∃∃V2,T2. ⦃G, L⦄ ⊢ ⓑ{b,I}V1.T1 ➡[h, r] ⓑ{b,I}V2.T2 &
                                    T = -ⓑ{I}V2.T2.
#h #r #I #G #L #V1 #T1 #T #H #b elim (cpg_inv_bind1 … H) -H *
[ #rV #rT #V2 #T2 #HV12 #HT12 #H1 #H2 destruct /3 width=4 by cpg_bind, ex2_2_intro/
| #r #T2 #_ #_ #H destruct
]
qed-.
