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

include "basic_2/substitution/ldrop.ma".
include "basic_2/static/sh.ma".

(* STATIC TYPE ASSIGNMENT ON TERMS ******************************************)

inductive sta (h:sh): lenv → relation term ≝
| sta_sort: ∀L,k. sta h L (⋆k) (⋆(next h k))
| sta_ldef: ∀L,K,V,W,U,i. ⇩[0, i] L ≡ K. ⓓV → sta h K V W →
            ⇧[0, i + 1] W ≡ U → sta h L (#i) U
| sta_ldec: ∀L,K,W,V,U,i. ⇩[0, i] L ≡ K. ⓛW → sta h K W V →
            ⇧[0, i + 1] W ≡ U → sta h L (#i) U
| sta_bind: ∀I,L,V,T,U. sta h (L. ⓑ{I} V) T U →
            sta h L (ⓑ{I}V.T) (ⓑ{I}V.U)
| sta_appl: ∀L,V,T,U. sta h L T U →
            sta h L (ⓐV.T) (ⓐV.U)
| sta_cast: ∀L,W,T,U. sta h L T U → sta h L (ⓝW. T) U
.

interpretation "static type assignment (term)"
   'StaticType h L T U = (sta h L T U).

(* Basic inversion lemmas ************************************************)

fact sta_inv_sort1_aux: ∀h,L,T,U. ⦃h, L⦄ ⊢ T • U → ∀k0. T = ⋆k0 →
                        U = ⋆(next h k0).
#h #L #T #U * -L -T -U
[ #L #k #k0 #H destruct //
| #L #K #V #W #U #i #_ #_ #_ #k0 #H destruct
| #L #K #W #V #U #i #_ #_ #_ #k0 #H destruct
| #I #L #V #T #U #_ #k0 #H destruct
| #L #V #T #U #_ #k0 #H destruct
| #L #W #T #U #_ #k0 #H destruct
qed.

(* Basic_1: was: sty0_gen_sort *)
lemma sta_inv_sort1: ∀h,L,U,k. ⦃h, L⦄ ⊢ ⋆k • U → U = ⋆(next h k).
/2 width=4/ qed-.

fact sta_inv_lref1_aux: ∀h,L,T,U. ⦃h, L⦄ ⊢ T • U → ∀j. T = #j →
                        (∃∃K,V,W. ⇩[0, j] L ≡ K. ⓓV & ⦃h, K⦄ ⊢ V • W &
                                  ⇧[0, j + 1] W ≡ U
                        ) ∨
                        (∃∃K,W,V. ⇩[0, j] L ≡ K. ⓛW & ⦃h, K⦄ ⊢ W • V &
                                  ⇧[0, j + 1] W ≡ U
                        ).
#h #L #T #U * -L -T -U
[ #L #k #j #H destruct
| #L #K #V #W #U #i #HLK #HVW #HWU #j #H destruct /3 width=6/
| #L #K #W #V #U #i #HLK #HWV #HWU #j #H destruct /3 width=6/
| #I #L #V #T #U #_ #j #H destruct
| #L #V #T #U #_ #j #H destruct
| #L #W #T #U #_ #j #H destruct
]
qed.

(* Basic_1: was sty0_gen_lref *)
lemma sta_inv_lref1: ∀h,L,U,i. ⦃h, L⦄ ⊢ #i • U →
                     (∃∃K,V,W. ⇩[0, i] L ≡ K. ⓓV & ⦃h, K⦄ ⊢ V • W &
                               ⇧[0, i + 1] W ≡ U
                     ) ∨
                     (∃∃K,W,V. ⇩[0, i] L ≡ K. ⓛW & ⦃h, K⦄ ⊢ W • V &
                               ⇧[0, i + 1] W ≡ U
                     ).
/2 width=3/ qed-.

fact sta_inv_bind1_aux: ∀h,L,T,U. ⦃h, L⦄ ⊢ T • U → ∀J,X,Y. T = ⓑ{J}Y.X →
                        ∃∃Z. ⦃h, L.ⓑ{J}Y⦄ ⊢ X • Z & U = ⓑ{J}Y.Z.
#h #L #T #U * -L -T -U
[ #L #k #J #X #Y #H destruct
| #L #K #V #W #U #i #_ #_ #_ #J #X #Y #H destruct
| #L #K #W #V #U #i #_ #_ #_ #J #X #Y #H destruct
| #I #L #V #T #U #HTU #J #X #Y #H destruct /2 width=3/
| #L #V #T #U #_ #J #X #Y #H destruct
| #L #W #T #U #_ #J #X #Y #H destruct
]
qed.

(* Basic_1: was: sty0_gen_bind *)
lemma sta_inv_bind1: ∀h,J,L,Y,X,U. ⦃h, L⦄ ⊢ ⓑ{J}Y.X • U →
                     ∃∃Z. ⦃h, L.ⓑ{J}Y⦄ ⊢ X • Z & U = ⓑ{J}Y.Z.
/2 width=3/ qed-.

fact sta_inv_appl1_aux: ∀h,L,T,U. ⦃h, L⦄ ⊢ T • U → ∀X,Y. T = ⓐY.X →
                        ∃∃Z. ⦃h, L⦄ ⊢ X • Z & U = ⓐY.Z.
#h #L #T #U * -L -T -U
[ #L #k #X #Y #H destruct
| #L #K #V #W #U #i #_ #_ #_ #X #Y #H destruct
| #L #K #W #V #U #i #_ #_ #_ #X #Y #H destruct
| #I #L #V #T #U #_ #X #Y #H destruct
| #L #V #T #U #HTU #X #Y #H destruct /2 width=3/
| #L #W #T #U #_ #X #Y #H destruct
]
qed.

(* Basic_1: was: sty0_gen_appl *)
lemma sta_inv_appl1: ∀h,L,Y,X,U. ⦃h, L⦄ ⊢ ⓐY.X • U →
                     ∃∃Z. ⦃h, L⦄ ⊢ X • Z & U = ⓐY.Z.
/2 width=3/ qed-.

fact sta_inv_cast1_aux: ∀h,L,T,U. ⦃h, L⦄ ⊢ T • U → ∀X,Y. T = ⓝY.X →
                     ⦃h, L⦄ ⊢ X • U.
#h #L #T #U * -L -T -U
[ #L #k #X #Y #H destruct
| #L #K #V #W #U #i #_ #_ #_ #X #Y #H destruct
| #L #K #W #V #U #i #_ #_ #_ #X #Y #H destruct
| #I #L #V #T #U #_ #X #Y #H destruct
| #L #V #T #U #_ #X #Y #H destruct
| #L #W #T #U #HTU #X #Y #H destruct //
]
qed.

(* Basic_1: was: sty0_gen_cast *)
lemma sta_inv_cast1: ∀h,L,X,Y,U. ⦃h, L⦄ ⊢ ⓝY.X • U →  ⦃h, L⦄ ⊢ X • U.
/2 width=4/ qed-.
