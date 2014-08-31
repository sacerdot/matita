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

include "basic_2/notation/relations/statictypestar_6.ma".
include "basic_2/grammar/genv.ma".
include "basic_2/substitution/drop.ma".
include "basic_2/static/sh.ma".

(* NAT-ITERATED STATIC TYPE ASSIGNMENT FOR TERMS ****************************)

(* activate genv *)
inductive lstas (h): nat → relation4 genv lenv term term ≝
| lstas_sort: ∀G,L,l,k. lstas h l G L (⋆k) (⋆((next h)^l k))
| lstas_ldef: ∀G,L,K,V,W,U,i,l. ⇩[i] L ≡ K.ⓓV → lstas h l G K V W →
              ⇧[0, i+1] W ≡ U → lstas h l G L (#i) U
| lstas_zero: ∀G,L,K,W,V,i. ⇩[i] L ≡ K.ⓛW → lstas h 0 G K W V →
              lstas h 0 G L (#i) (#i)
| lstas_succ: ∀G,L,K,W,V,U,i,l. ⇩[i] L ≡ K.ⓛW → lstas h l G K W V →
              ⇧[0, i+1] V ≡ U → lstas h (l+1) G L (#i) U
| lstas_bind: ∀a,I,G,L,V,T,U,l. lstas h l G (L.ⓑ{I}V) T U →
              lstas h l G L (ⓑ{a,I}V.T) (ⓑ{a,I}V.U)
| lstas_appl: ∀G,L,V,T,U,l. lstas h l G L T U → lstas h l G L (ⓐV.T) (ⓐV.U)
| lstas_cast: ∀G,L,W,T,U,l. lstas h l G L T U → lstas h l G L (ⓝW.T) U
.

interpretation "nat-iterated static type assignment (term)"
   'StaticTypeStar h G L l T U = (lstas h l G L T U).

(* Basic inversion lemmas ***************************************************)

fact lstas_inv_sort1_aux: ∀h,G,L,T,U,l. ⦃G, L⦄ ⊢ T •*[h, l] U → ∀k0. T = ⋆k0 →
                          U = ⋆((next h)^l k0).
#h #G #L #T #U #l * -G -L -T -U -l
[ #G #L #l #k #k0 #H destruct //
| #G #L #K #V #W #U #i #l #_ #_ #_ #k0 #H destruct
| #G #L #K #W #V #i #_ #_ #k0 #H destruct
| #G #L #K #W #V #U #i #l #_ #_ #_ #k0 #H destruct
| #a #I #G #L #V #T #U #l #_ #k0 #H destruct
| #G #L #V #T #U #l #_ #k0 #H destruct
| #G #L #W #T #U #l #_ #k0 #H destruct
qed-.

(* Basic_1: was just: sty0_gen_sort *)
lemma lstas_inv_sort1: ∀h,G,L,X,k,l. ⦃G, L⦄ ⊢ ⋆k •*[h, l] X → X = ⋆((next h)^l k).
/2 width=5 by lstas_inv_sort1_aux/
qed-.

fact lstas_inv_lref1_aux: ∀h,G,L,T,U,l. ⦃G, L⦄ ⊢ T •*[h, l] U → ∀j. T = #j → ∨∨
                          (∃∃K,V,W. ⇩[j] L ≡ K.ⓓV & ⦃G, K⦄ ⊢ V •*[h, l] W &
                                    ⇧[0, j+1] W ≡ U
                          ) |
                          (∃∃K,W,V. ⇩[j] L ≡ K.ⓛW & ⦃G, K⦄ ⊢ W •*[h, 0] V & 
                                    U = #j & l = 0
                          ) |
                          (∃∃K,W,V,l0. ⇩[j] L ≡ K.ⓛW & ⦃G, K⦄ ⊢ W •*[h, l0] V &
                                       ⇧[0, j+1] V ≡ U & l = l0+1
                          ).
#h #G #L #T #U #l * -G -L -T -U -l
[ #G #L #l #k #j #H destruct
| #G #L #K #V #W #U #i #l #HLK #HVW #HWU #j #H destruct /3 width=6 by or3_intro0, ex3_3_intro/
| #G #L #K #W #V #i #HLK #HWV #j #H destruct /3 width=5 by or3_intro1, ex4_3_intro/
| #G #L #K #W #V #U #i #l #HLK #HWV #HWU #j #H destruct /3 width=8 by or3_intro2, ex4_4_intro/ 
| #a #I #G #L #V #T #U #l #_ #j #H destruct
| #G #L #V #T #U #l #_ #j #H destruct
| #G #L #W #T #U #l #_ #j #H destruct
]
qed-.

lemma lstas_inv_lref1: ∀h,G,L,X,i,l. ⦃G, L⦄ ⊢ #i •*[h, l] X → ∨∨
                       (∃∃K,V,W. ⇩[i] L ≡ K.ⓓV & ⦃G, K⦄ ⊢ V •*[h, l] W &
                                 ⇧[0, i+1] W ≡ X
                       ) |
                       (∃∃K,W,V. ⇩[i] L ≡ K.ⓛW & ⦃G, K⦄ ⊢ W •*[h, 0] V & 
                                 X = #i & l = 0
                       ) |                      
                       (∃∃K,W,V,l0. ⇩[i] L ≡ K.ⓛW & ⦃G, K⦄ ⊢ W •*[h, l0] V &
                                    ⇧[0, i+1] V ≡ X & l = l0+1
                       ).
/2 width=3 by lstas_inv_lref1_aux/
qed-.

lemma lstas_inv_lref1_O: ∀h,G,L,X,i. ⦃G, L⦄ ⊢ #i •*[h, 0] X →
                         (∃∃K,V,W. ⇩[i] L ≡ K.ⓓV & ⦃G, K⦄ ⊢ V •*[h, 0] W &
                                   ⇧[0, i+1] W ≡ X
                         ) ∨
                         (∃∃K,W,V. ⇩[i] L ≡ K.ⓛW & ⦃G, K⦄ ⊢ W •*[h, 0] V & 
                                   X = #i
                         ).
#h #G #L #X #i #H elim (lstas_inv_lref1 … H) -H * /3 width=6 by ex3_3_intro, or_introl, or_intror/
#K #W #V #l #_ #_ #_ <plus_n_Sm #H destruct
qed-.

(* Basic_1: was just: sty0_gen_lref *)
lemma lstas_inv_lref1_S: ∀h,G,L,X,i,l. ⦃G, L⦄ ⊢ #i •*[h, l+1] X →
                         (∃∃K,V,W. ⇩[i] L ≡ K.ⓓV & ⦃G, K⦄ ⊢ V •*[h, l+1] W &
                                   ⇧[0, i+1] W ≡ X
                         ) ∨                      
                         (∃∃K,W,V. ⇩[i] L ≡ K.ⓛW & ⦃G, K⦄ ⊢ W •*[h, l] V &
                                   ⇧[0, i+1] V ≡ X
                         ).
#h #G #L #X #i #l #H elim (lstas_inv_lref1 … H) -H * /3 width=6 by ex3_3_intro, or_introl, or_intror/
#K #W #V #_ #_ #_ <plus_n_Sm #H destruct
qed-.

fact lstas_inv_gref1_aux: ∀h,G,L,T,U,l. ⦃G, L⦄ ⊢ T •*[h, l] U → ∀p0. T = §p0 → ⊥.
#h #G #L #T #U #l * -G -L -T -U -l
[ #G #L #l #k #p0 #H destruct
| #G #L #K #V #W #U #i #l #_ #_ #_ #p0 #H destruct
| #G #L #K #W #V #i #_ #_ #p0 #H destruct
| #G #L #K #W #V #U #i #l #_ #_ #_ #p0 #H destruct
| #a #I #G #L #V #T #U #l #_ #p0 #H destruct
| #G #L #V #T #U #l #_ #p0 #H destruct
| #G #L #W #T #U #l #_ #p0 #H destruct
qed-.

lemma lstas_inv_gref1: ∀h,G,L,X,p,l. ⦃G, L⦄ ⊢ §p •*[h, l] X → ⊥.
/2 width=9 by lstas_inv_gref1_aux/
qed-.

fact lstas_inv_bind1_aux: ∀h,G,L,T,U,l. ⦃G, L⦄ ⊢ T •*[h, l] U → ∀b,J,X,Y. T = ⓑ{b,J}Y.X →
                          ∃∃Z. ⦃G, L.ⓑ{J}Y⦄ ⊢ X •*[h, l] Z & U = ⓑ{b,J}Y.Z.
#h #G #L #T #U #l * -G -L -T -U -l
[ #G #L #l #k #b #J #X #Y #H destruct
| #G #L #K #V #W #U #i #l #_ #_ #_ #b #J #X #Y #H destruct
| #G #L #K #W #V #i #_ #_ #b #J #X #Y #H destruct
| #G #L #K #W #V #U #i #l #_ #_ #_ #b #J #X #Y #H destruct
| #a #I #G #L #V #T #U #l #HTU #b #J #X #Y #H destruct /2 width=3 by ex2_intro/
| #G #L #V #T #U #l #_ #b #J #X #Y #H destruct
| #G #L #W #T #U #l #_ #b #J #X #Y #H destruct
]
qed-.

(* Basic_1: was just: sty0_gen_bind *)
lemma lstas_inv_bind1: ∀h,a,I,G,L,V,T,X,l. ⦃G, L⦄ ⊢ ⓑ{a,I}V.T •*[h, l] X →
                       ∃∃U. ⦃G, L.ⓑ{I}V⦄ ⊢ T •*[h, l] U & X = ⓑ{a,I}V.U.
/2 width=3 by lstas_inv_bind1_aux/
qed-.

fact lstas_inv_appl1_aux: ∀h,G,L,T,U,l. ⦃G, L⦄ ⊢ T •*[h, l] U → ∀X,Y. T = ⓐY.X →
                          ∃∃Z. ⦃G, L⦄ ⊢ X •*[h, l] Z & U = ⓐY.Z.
#h #G #L #T #U #l * -G -L -T -U -l
[ #G #L #l #k #X #Y #H destruct
| #G #L #K #V #W #U #i #l #_ #_ #_ #X #Y #H destruct
| #G #L #K #W #V #i #_ #_ #X #Y #H destruct
| #G #L #K #W #V #U #i #l #_ #_ #_ #X #Y #H destruct
| #a #I #G #L #V #T #U #l #_ #X #Y #H destruct
| #G #L #V #T #U #l #HTU #X #Y #H destruct /2 width=3 by ex2_intro/
| #G #L #W #T #U #l #_ #X #Y #H destruct
]
qed-.

(* Basic_1: was just: sty0_gen_appl *)
lemma lstas_inv_appl1: ∀h,G,L,V,T,X,l. ⦃G, L⦄ ⊢ ⓐV.T •*[h, l] X →
                       ∃∃U. ⦃G, L⦄ ⊢ T •*[h, l] U & X = ⓐV.U.
/2 width=3 by lstas_inv_appl1_aux/
qed-.

fact lstas_inv_cast1_aux: ∀h,G,L,T,U,l. ⦃G, L⦄ ⊢ T •*[h, l] U → ∀X,Y. T = ⓝY.X →
                          ⦃G, L⦄ ⊢ X •*[h, l] U.
#h #G #L #T #U #l * -G -L -T -U -l
[ #G #L #l #k #X #Y #H destruct
| #G #L #K #V #W #U #i #l #_ #_ #_ #X #Y #H destruct
| #G #L #K #W #V #i #_ #_ #X #Y #H destruct
| #G #L #K #W #V #U #i #l #_ #_ #_ #X #Y #H destruct
| #a #I #G #L #V #T #U #l #_ #X #Y #H destruct
| #G #L #V #T #U #l #_ #X #Y #H destruct
| #G #L #W #T #U #l #HTU #X #Y #H destruct //
]
qed-.

(* Basic_1: was just: sty0_gen_cast *)
lemma lstas_inv_cast1: ∀h,G,L,W,T,U,l. ⦃G, L⦄ ⊢ ⓝW.T •*[h, l] U → ⦃G, L⦄ ⊢ T •*[h, l] U.
/2 width=4 by lstas_inv_cast1_aux/
qed-.

(* Basic_1: removed theorems 7:
            sty1_abbr sty1_appl sty1_bind sty1_cast2
            sty1_correct sty1_lift sty1_trans
*)
