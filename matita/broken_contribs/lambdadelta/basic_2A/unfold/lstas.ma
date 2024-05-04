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

include "ground/xoa/ex_4_3.ma".
include "ground/xoa/ex_4_4.ma".
include "basic_2A/notation/relations/statictypestar_6.ma".
include "basic_2A/grammar/genv.ma".
include "basic_2A/substitution/drop.ma".
include "basic_2A/static/sh.ma".

(* NAT-ITERATED STATIC TYPE ASSIGNMENT FOR TERMS ****************************)

(* activate genv *)
inductive lstas (h): nat → relation4 genv lenv term term ≝
| lstas_sort: ∀G,L,d,k. lstas h d G L (⋆k) (⋆((next h)^d k))
| lstas_ldef: ∀G,L,K,V,W,U,i,d. ⬇[i] L ≡ K.ⓓV → lstas h d G K V W →
              ⬆[0, i+1] W ≡ U → lstas h d G L (#i) U
| lstas_zero: ∀G,L,K,W,V,i. ⬇[i] L ≡ K.ⓛW → lstas h 0 G K W V →
              lstas h 0 G L (#i) (#i)
| lstas_succ: ∀G,L,K,W,V,U,i,d. ⬇[i] L ≡ K.ⓛW → lstas h d G K W V →
              ⬆[0, i+1] V ≡ U → lstas h (d+1) G L (#i) U
| lstas_bind: ∀a,I,G,L,V,T,U,d. lstas h d G (L.ⓑ{I}V) T U →
              lstas h d G L (ⓑ{a,I}V.T) (ⓑ{a,I}V.U)
| lstas_appl: ∀G,L,V,T,U,d. lstas h d G L T U → lstas h d G L (ⓐV.T) (ⓐV.U)
| lstas_cast: ∀G,L,W,T,U,d. lstas h d G L T U → lstas h d G L (ⓝW.T) U
.

interpretation "nat-iterated static type assignment (term)"
   'StaticTypeStar h G L d T U = (lstas h d G L T U).

(* Basic inversion lemmas ***************************************************)

fact lstas_inv_sort1_aux: ∀h,G,L,T,U,d. ⦃G, L⦄ ⊢ T •*[h, d] U → ∀k0. T = ⋆k0 →
                          U = ⋆((next h)^d k0).
#h #G #L #T #U #d * -G -L -T -U -d
[ #G #L #d #k #k0 #H destruct //
| #G #L #K #V #W #U #i #d #_ #_ #_ #k0 #H destruct
| #G #L #K #W #V #i #_ #_ #k0 #H destruct
| #G #L #K #W #V #U #i #d #_ #_ #_ #k0 #H destruct
| #a #I #G #L #V #T #U #d #_ #k0 #H destruct
| #G #L #V #T #U #d #_ #k0 #H destruct
| #G #L #W #T #U #d #_ #k0 #H destruct
qed-.

lemma lstas_inv_sort1: ∀h,G,L,X,k,d. ⦃G, L⦄ ⊢ ⋆k •*[h, d] X → X = ⋆((next h)^d k).
/2 width=5 by lstas_inv_sort1_aux/
qed-.

fact lstas_inv_lref1_aux: ∀h,G,L,T,U,d. ⦃G, L⦄ ⊢ T •*[h, d] U → ∀j. T = #j → ∨∨
                          (∃∃K,V,W. ⬇[j] L ≡ K.ⓓV & ⦃G, K⦄ ⊢ V •*[h, d] W &
                                    ⬆[0, j+1] W ≡ U
                          ) |
                          (∃∃K,W,V. ⬇[j] L ≡ K.ⓛW & ⦃G, K⦄ ⊢ W •*[h, 0] V &
                                    U = #j & d = 0
                          ) |
                          (∃∃K,W,V,d0. ⬇[j] L ≡ K.ⓛW & ⦃G, K⦄ ⊢ W •*[h, d0] V &
                                       ⬆[0, j+1] V ≡ U & d = d0+1
                          ).
#h #G #L #T #U #d * -G -L -T -U -d
[ #G #L #d #k #j #H destruct
| #G #L #K #V #W #U #i #d #HLK #HVW #HWU #j #H destruct /3 width=6 by or3_intro0, ex3_3_intro/
| #G #L #K #W #V #i #HLK #HWV #j #H destruct /3 width=5 by or3_intro1, ex4_3_intro/
| #G #L #K #W #V #U #i #d #HLK #HWV #HWU #j #H destruct /3 width=8 by or3_intro2, ex4_4_intro/
| #a #I #G #L #V #T #U #d #_ #j #H destruct
| #G #L #V #T #U #d #_ #j #H destruct
| #G #L #W #T #U #d #_ #j #H destruct
]
qed-.

lemma lstas_inv_lref1: ∀h,G,L,X,i,d. ⦃G, L⦄ ⊢ #i •*[h, d] X → ∨∨
                       (∃∃K,V,W. ⬇[i] L ≡ K.ⓓV & ⦃G, K⦄ ⊢ V •*[h, d] W &
                                 ⬆[0, i+1] W ≡ X
                       ) |
                       (∃∃K,W,V. ⬇[i] L ≡ K.ⓛW & ⦃G, K⦄ ⊢ W •*[h, 0] V &
                                 X = #i & d = 0
                       ) |
                       (∃∃K,W,V,d0. ⬇[i] L ≡ K.ⓛW & ⦃G, K⦄ ⊢ W •*[h, d0] V &
                                    ⬆[0, i+1] V ≡ X & d = d0+1
                       ).
/2 width=3 by lstas_inv_lref1_aux/
qed-.

lemma lstas_inv_lref1_O: ∀h,G,L,X,i. ⦃G, L⦄ ⊢ #i •*[h, 0] X →
                         (∃∃K,V,W. ⬇[i] L ≡ K.ⓓV & ⦃G, K⦄ ⊢ V •*[h, 0] W &
                                   ⬆[0, i+1] W ≡ X
                         ) ∨
                         (∃∃K,W,V. ⬇[i] L ≡ K.ⓛW & ⦃G, K⦄ ⊢ W •*[h, 0] V &
                                   X = #i
                         ).
#h #G #L #X #i #H elim (lstas_inv_lref1 … H) -H * /3 width=6 by ex3_3_intro, or_introl, or_intror/
#K #W #V #d #_ #_ #_ <plus_n_Sm #H destruct
qed-.

lemma lstas_inv_lref1_S: ∀h,G,L,X,i,d. ⦃G, L⦄ ⊢ #i •*[h, d+1] X →
                         (∃∃K,V,W. ⬇[i] L ≡ K.ⓓV & ⦃G, K⦄ ⊢ V •*[h, d+1] W &
                                   ⬆[0, i+1] W ≡ X
                         ) ∨
                         (∃∃K,W,V. ⬇[i] L ≡ K.ⓛW & ⦃G, K⦄ ⊢ W •*[h, d] V &
                                   ⬆[0, i+1] V ≡ X
                         ).
#h #G #L #X #i #d #H elim (lstas_inv_lref1 … H) -H * /3 width=6 by ex3_3_intro, or_introl, or_intror/
#K #W #V #_ #_ #_ <plus_n_Sm #H destruct
qed-.

fact lstas_inv_gref1_aux: ∀h,G,L,T,U,d. ⦃G, L⦄ ⊢ T •*[h, d] U → ∀p0. T = §p0 → ⊥.
#h #G #L #T #U #d * -G -L -T -U -d
[ #G #L #d #k #p0 #H destruct
| #G #L #K #V #W #U #i #d #_ #_ #_ #p0 #H destruct
| #G #L #K #W #V #i #_ #_ #p0 #H destruct
| #G #L #K #W #V #U #i #d #_ #_ #_ #p0 #H destruct
| #a #I #G #L #V #T #U #d #_ #p0 #H destruct
| #G #L #V #T #U #d #_ #p0 #H destruct
| #G #L #W #T #U #d #_ #p0 #H destruct
qed-.

lemma lstas_inv_gref1: ∀h,G,L,X,p,d. ⦃G, L⦄ ⊢ §p •*[h, d] X → ⊥.
/2 width=9 by lstas_inv_gref1_aux/
qed-.

fact lstas_inv_bind1_aux: ∀h,G,L,T,U,d. ⦃G, L⦄ ⊢ T •*[h, d] U → ∀b,J,X,Y. T = ⓑ{b,J}Y.X →
                          ∃∃Z. ⦃G, L.ⓑ{J}Y⦄ ⊢ X •*[h, d] Z & U = ⓑ{b,J}Y.Z.
#h #G #L #T #U #d * -G -L -T -U -d
[ #G #L #d #k #b #J #X #Y #H destruct
| #G #L #K #V #W #U #i #d #_ #_ #_ #b #J #X #Y #H destruct
| #G #L #K #W #V #i #_ #_ #b #J #X #Y #H destruct
| #G #L #K #W #V #U #i #d #_ #_ #_ #b #J #X #Y #H destruct
| #a #I #G #L #V #T #U #d #HTU #b #J #X #Y #H destruct /2 width=3 by ex2_intro/
| #G #L #V #T #U #d #_ #b #J #X #Y #H destruct
| #G #L #W #T #U #d #_ #b #J #X #Y #H destruct
]
qed-.

lemma lstas_inv_bind1: ∀h,a,I,G,L,V,T,X,d. ⦃G, L⦄ ⊢ ⓑ{a,I}V.T •*[h, d] X →
                       ∃∃U. ⦃G, L.ⓑ{I}V⦄ ⊢ T •*[h, d] U & X = ⓑ{a,I}V.U.
/2 width=3 by lstas_inv_bind1_aux/
qed-.

fact lstas_inv_appl1_aux: ∀h,G,L,T,U,d. ⦃G, L⦄ ⊢ T •*[h, d] U → ∀X,Y. T = ⓐY.X →
                          ∃∃Z. ⦃G, L⦄ ⊢ X •*[h, d] Z & U = ⓐY.Z.
#h #G #L #T #U #d * -G -L -T -U -d
[ #G #L #d #k #X #Y #H destruct
| #G #L #K #V #W #U #i #d #_ #_ #_ #X #Y #H destruct
| #G #L #K #W #V #i #_ #_ #X #Y #H destruct
| #G #L #K #W #V #U #i #d #_ #_ #_ #X #Y #H destruct
| #a #I #G #L #V #T #U #d #_ #X #Y #H destruct
| #G #L #V #T #U #d #HTU #X #Y #H destruct /2 width=3 by ex2_intro/
| #G #L #W #T #U #d #_ #X #Y #H destruct
]
qed-.

lemma lstas_inv_appl1: ∀h,G,L,V,T,X,d. ⦃G, L⦄ ⊢ ⓐV.T •*[h, d] X →
                       ∃∃U. ⦃G, L⦄ ⊢ T •*[h, d] U & X = ⓐV.U.
/2 width=3 by lstas_inv_appl1_aux/
qed-.

fact lstas_inv_cast1_aux: ∀h,G,L,T,U,d. ⦃G, L⦄ ⊢ T •*[h, d] U → ∀X,Y. T = ⓝY.X →
                          ⦃G, L⦄ ⊢ X •*[h, d] U.
#h #G #L #T #U #d * -G -L -T -U -d
[ #G #L #d #k #X #Y #H destruct
| #G #L #K #V #W #U #i #d #_ #_ #_ #X #Y #H destruct
| #G #L #K #W #V #i #_ #_ #X #Y #H destruct
| #G #L #K #W #V #U #i #d #_ #_ #_ #X #Y #H destruct
| #a #I #G #L #V #T #U #d #_ #X #Y #H destruct
| #G #L #V #T #U #d #_ #X #Y #H destruct
| #G #L #W #T #U #d #HTU #X #Y #H destruct //
]
qed-.

lemma lstas_inv_cast1: ∀h,G,L,W,T,U,d. ⦃G, L⦄ ⊢ ⓝW.T •*[h, d] U → ⦃G, L⦄ ⊢ T •*[h, d] U.
/2 width=4 by lstas_inv_cast1_aux/
qed-.
