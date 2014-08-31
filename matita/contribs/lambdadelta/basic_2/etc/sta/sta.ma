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

include "basic_2/notation/relations/statictype_5.ma".
include "basic_2/grammar/genv.ma".
include "basic_2/substitution/drop.ma".
include "basic_2/static/sh.ma".

(* STATIC TYPE ASSIGNMENT ON TERMS ******************************************)

(* activate genv *)
inductive sta (h:sh): relation4 genv lenv term term ≝
| sta_sort: ∀G,L,k. sta h G L (⋆k) (⋆(next h k))
| sta_ldef: ∀G,L,K,V,W,U,i. ⇩[i] L ≡ K.ⓓV → sta h G K V W →
            ⇧[0, i + 1] W ≡ U → sta h G L (#i) U
| sta_ldec: ∀G,L,K,W,V,U,i. ⇩[i] L ≡ K.ⓛW → sta h G K W V →
            ⇧[0, i + 1] W ≡ U → sta h G L (#i) U
| sta_bind: ∀a,I,G,L,V,T,U. sta h G (L.ⓑ{I}V) T U →
            sta h G L (ⓑ{a,I}V.T) (ⓑ{a,I}V.U)
| sta_appl: ∀G,L,V,T,U. sta h G L T U → sta h G L (ⓐV.T) (ⓐV.U)
| sta_cast: ∀G,L,W,T,U. sta h G L T U → sta h G L (ⓝW.T) U
.

interpretation "static type assignment (term)"
   'StaticType h G L T U = (sta h G L T U).

(* Basic inversion lemmas ************************************************)

fact sta_inv_sort1_aux: ∀h,G,L,T,U. ⦃G, L⦄ ⊢ T •[h] U → ∀k0. T = ⋆k0 →
                        U = ⋆(next h k0).
#h #G #L #T #U * -G -L -T -U
[ #G #L #k #k0 #H destruct //
| #G #L #K #V #W #U #i #_ #_ #_ #k0 #H destruct
| #G #L #K #W #V #U #i #_ #_ #_ #k0 #H destruct
| #a #I #G #L #V #T #U #_ #k0 #H destruct
| #G #L #V #T #U #_ #k0 #H destruct
| #G #L #W #T #U #_ #k0 #H destruct
qed-.

(* Basic_1: was: sty0_gen_sort *)
lemma sta_inv_sort1: ∀h,G,L,U,k. ⦃G, L⦄ ⊢ ⋆k •[h] U → U = ⋆(next h k).
/2 width=5 by sta_inv_sort1_aux/ qed-.

fact sta_inv_lref1_aux: ∀h,G,L,T,U. ⦃G, L⦄ ⊢ T •[h] U → ∀j. T = #j →
                        (∃∃K,V,W. ⇩[j] L ≡ K.ⓓV & ⦃G, K⦄ ⊢ V •[h] W &
                                  ⇧[0, j+1] W ≡ U
                        ) ∨
                        (∃∃K,W,V. ⇩[j] L ≡ K.ⓛW & ⦃G, K⦄ ⊢ W •[h] V &
                                  ⇧[0, j+1] W ≡ U
                        ).
#h #G #L #T #U * -G -L -T -U
[ #G #L #k #j #H destruct
| #G #L #K #V #W #U #i #HLK #HVW #HWU #j #H destruct /3 width=6 by or_introl, ex3_3_intro/
| #G #L #K #W #V #U #i #HLK #HWV #HWU #j #H destruct /3 width=6 by or_intror, ex3_3_intro/
| #a #I #G #L #V #T #U #_ #j #H destruct
| #G #L #V #T #U #_ #j #H destruct
| #G #L #W #T #U #_ #j #H destruct
]
qed-.

(* Basic_1: was sty0_gen_lref *)
lemma sta_inv_lref1: ∀h,G,L,U,i. ⦃G, L⦄ ⊢ #i •[h] U →
                     (∃∃K,V,W. ⇩[i] L ≡ K.ⓓV & ⦃G, K⦄ ⊢ V •[h] W &
                               ⇧[0, i+1] W ≡ U
                     ) ∨
                     (∃∃K,W,V. ⇩[i] L ≡ K.ⓛW & ⦃G, K⦄ ⊢ W •[h] V &
                               ⇧[0, i+1] W ≡ U
                     ).
/2 width=3 by sta_inv_lref1_aux/ qed-.

fact sta_inv_gref1_aux: ∀h,G,L,T,U. ⦃G, L⦄ ⊢ T •[h] U → ∀p0. T = §p0 → ⊥.
#h #G #L #T #U * -G -L -T -U
[ #G #L #k #p0 #H destruct
| #G #L #K #V #W #U #i #_ #_ #_ #p0 #H destruct
| #G #L #K #W #V #U #i #_ #_ #_ #p0 #H destruct
| #a #I #G #L #V #T #U #_ #p0 #H destruct
| #G #L #V #T #U #_ #p0 #H destruct
| #G #L #W #T #U #_ #p0 #H destruct
qed-.

lemma sta_inv_gref1: ∀h,G,L,U,p. ⦃G, L⦄ ⊢ §p •[h] U → ⊥.
/2 width=8 by sta_inv_gref1_aux/ qed-.

fact sta_inv_bind1_aux: ∀h,G,L,T,U. ⦃G, L⦄ ⊢ T •[h] U → ∀b,J,X,Y. T = ⓑ{b,J}Y.X →
                        ∃∃Z. ⦃G, L.ⓑ{J}Y⦄ ⊢ X •[h] Z & U = ⓑ{b,J}Y.Z.
#h #G #L #T #U * -G -L -T -U
[ #G #L #k #b #J #X #Y #H destruct
| #G #L #K #V #W #U #i #_ #_ #_ #b #J #X #Y #H destruct
| #G #L #K #W #V #U #i #_ #_ #_ #b #J #X #Y #H destruct
| #a #I #G #L #V #T #U #HTU #b #J #X #Y #H destruct /2 width=3 by ex2_intro/
| #G #L #V #T #U #_ #b #J #X #Y #H destruct
| #G #L #W #T #U #_ #b #J #X #Y #H destruct
]
qed-.

(* Basic_1: was: sty0_gen_bind *)
lemma sta_inv_bind1: ∀h,b,J,G,L,Y,X,U. ⦃G, L⦄ ⊢ ⓑ{b,J}Y.X •[h] U →
                     ∃∃Z. ⦃G, L.ⓑ{J}Y⦄ ⊢ X •[h] Z & U = ⓑ{b,J}Y.Z.
/2 width=3 by sta_inv_bind1_aux/ qed-.

fact sta_inv_appl1_aux: ∀h,G,L,T,U. ⦃G, L⦄ ⊢ T •[h] U → ∀X,Y. T = ⓐY.X →
                        ∃∃Z. ⦃G, L⦄ ⊢ X •[h] Z & U = ⓐY.Z.
#h #G #L #T #U * -G -L -T -U
[ #G #L #k #X #Y #H destruct
| #G #L #K #V #W #U #i #_ #_ #_ #X #Y #H destruct
| #G #L #K #W #V #U #i #_ #_ #_ #X #Y #H destruct
| #a #I #G #L #V #T #U #_ #X #Y #H destruct
| #G #L #V #T #U #HTU #X #Y #H destruct /2 width=3 by ex2_intro/
| #G #L #W #T #U #_ #X #Y #H destruct
]
qed-.

(* Basic_1: was: sty0_gen_appl *)
lemma sta_inv_appl1: ∀h,G,L,Y,X,U. ⦃G, L⦄ ⊢ ⓐY.X •[h] U →
                     ∃∃Z. ⦃G, L⦄ ⊢ X •[h] Z & U = ⓐY.Z.
/2 width=3 by sta_inv_appl1_aux/ qed-.

fact sta_inv_cast1_aux: ∀h,G,L,T,U. ⦃G, L⦄ ⊢ T •[h] U → ∀X,Y. T = ⓝY.X →
                     ⦃G, L⦄ ⊢ X •[h] U.
#h #G #L #T #U * -G -L -T -U
[ #G #L #k #X #Y #H destruct
| #G #L #K #V #W #U #i #_ #_ #_ #X #Y #H destruct
| #G #L #K #W #V #U #i #_ #_ #_ #X #Y #H destruct
| #a #I #G #L #V #T #U #_ #X #Y #H destruct
| #G #L #V #T #U #_ #X #Y #H destruct
| #G #L #W #T #U #HTU #X #Y #H destruct //
]
qed-.

(* Basic_1: was: sty0_gen_cast *)
lemma sta_inv_cast1: ∀h,G,L,X,Y,U. ⦃G, L⦄ ⊢ ⓝY.X •[h] U → ⦃G, L⦄ ⊢ X •[h] U.
/2 width=4 by sta_inv_cast1_aux/ qed-.
