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
include "basic_2/static/sd.ma".

(* STRATIFIED STATIC TYPE ASSIGNMENT ON TERMS *******************************)

inductive ssta (h:sh) (g:sd h): nat → lenv → relation term ≝
| ssta_sort: ∀L,k,l. deg h g k l → ssta h g l L (⋆k) (⋆(next h k))
| ssta_ldef: ∀L,K,V,W,U,i,l. ⇩[0, i] L ≡ K. ⓓV → ssta h g l K V W →
             ⇧[0, i + 1] W ≡ U → ssta h g l L (#i) U
| ssta_ldec: ∀L,K,W,V,U,i,l. ⇩[0, i] L ≡ K. ⓛW → ssta h g l K W V →
             ⇧[0, i + 1] W ≡ U → ssta h g (l+1) L (#i) U
| ssta_bind: ∀I,L,V,T,U,l. ssta h g l (L. ⓑ{I} V) T U →
             ssta h g l L (ⓑ{I}V.T) (ⓑ{I}V.U)
| ssta_appl: ∀L,V,T,U,l. ssta h g l L T U →
             ssta h g l L (ⓐV.T) (ⓐV.U)
| ssta_cast: ∀L,V,W,T,U,l. ssta h g (l - 1) L V W → ssta h g l L T U →
                           ssta h g l L (ⓝV. T) (ⓝW. U)
.

interpretation "stratified static type assignment (term)"
   'StaticType h g l L T U = (ssta h g l L T U).

(* Basic inversion lemmas ************************************************)

fact ssta_inv_sort1_aux: ∀h,g,L,T,U,l. ⦃h, L⦄ ⊢ T •[g, l] U → ∀k0. T = ⋆k0 →
                         deg h g k0 l ∧ U = ⋆(next h k0).
#h #g #L #T #U #l * -L -T -U -l
[ #L #k #l #Hkl #k0 #H destruct /2 width=1/
| #L #K #V #W #U #i #l #_ #_ #_ #k0 #H destruct
| #L #K #W #V #U #i #l #_ #_ #_ #k0 #H destruct
| #I #L #V #T #U #l #_ #k0 #H destruct
| #L #V #T #U #l #_ #k0 #H destruct
| #L #V #W #T #U #l #_ #_ #k0 #H destruct
qed.

(* Basic_1: was just: sty0_gen_sort *)
lemma ssta_inv_sort1: ∀h,g,L,U,k,l. ⦃h, L⦄ ⊢ ⋆k •[g, l] U →
                      deg h g k l ∧ U = ⋆(next h k).
/2 width=4/ qed-.

fact ssta_inv_lref1_aux: ∀h,g,L,T,U,l. ⦃h, L⦄ ⊢ T •[g, l] U → ∀j. T = #j →
                         (∃∃K,V,W. ⇩[0, j] L ≡ K. ⓓV & ⦃h, K⦄ ⊢ V •[g, l] W &
                                   ⇧[0, j + 1] W ≡ U
                         ) ∨
                         (∃∃K,W,V,l0. ⇩[0, j] L ≡ K. ⓛW & ⦃h, K⦄ ⊢ W •[g, l0] V &
                                      ⇧[0, j + 1] W ≡ U & l = l0 + 1
                         ).
#h #g #L #T #U #l * -L -T -U -l
[ #L #k #l #_ #j #H destruct
| #L #K #V #W #U #i #l #HLK #HVW #HWU #j #H destruct /3 width=6/
| #L #K #W #V #U #i #l #HLK #HWV #HWU #j #H destruct /3 width=8/
| #I #L #V #T #U #l #_ #j #H destruct
| #L #V #T #U #l #_ #j #H destruct
| #L #V #W #T #U #l #_ #_ #j #H destruct
]
qed.

(* Basic_1: was just: sty0_gen_lref *)
lemma ssta_inv_lref1: ∀h,g,L,U,i,l. ⦃h, L⦄ ⊢ #i •[g, l] U →
                      (∃∃K,V,W. ⇩[0, i] L ≡ K. ⓓV & ⦃h, K⦄ ⊢ V •[g, l] W &
                                ⇧[0, i + 1] W ≡ U
                      ) ∨
                      (∃∃K,W,V,l0. ⇩[0, i] L ≡ K. ⓛW & ⦃h, K⦄ ⊢ W •[g, l0] V &
                                   ⇧[0, i + 1] W ≡ U & l = l0 + 1
                      ).
/2 width=3/ qed-.

fact ssta_inv_bind1_aux: ∀h,g,L,T,U,l. ⦃h, L⦄ ⊢ T •[g, l] U →
                         ∀J,X,Y. T = ⓑ{J}Y.X →
                         ∃∃Z. ⦃h, L.ⓑ{J}Y⦄ ⊢ X •[g, l] Z & U = ⓑ{J}Y.Z.
#h #g #L #T #U #l * -L -T -U -l
[ #L #k #l #_ #J #X #Y #H destruct
| #L #K #V #W #U #i #l #_ #_ #_ #J #X #Y #H destruct
| #L #K #W #V #U #i #l #_ #_ #_ #J #X #Y #H destruct
| #I #L #V #T #U #l #HTU #J #X #Y #H destruct /2 width=3/
| #L #V #T #U #l #_ #J #X #Y #H destruct
| #L #V #W #T #U #l #_ #_ #J #X #Y #H destruct
]
qed.

(* Basic_1: was just: sty0_gen_bind *)
lemma ssta_inv_bind1: ∀h,g,J,L,Y,X,U,l. ⦃h, L⦄ ⊢ ⓑ{J}Y.X •[g, l] U →
                      ∃∃Z. ⦃h, L.ⓑ{J}Y⦄ ⊢ X •[g, l] Z & U = ⓑ{J}Y.Z.
/2 width=3/ qed-.

fact ssta_inv_appl1_aux: ∀h,g,L,T,U,l. ⦃h, L⦄ ⊢ T •[g, l] U → ∀X,Y. T = ⓐY.X →
                         ∃∃Z. ⦃h, L⦄ ⊢ X •[g, l] Z & U = ⓐY.Z.
#h #g #L #T #U #l * -L -T -U -l
[ #L #k #l #_ #X #Y #H destruct
| #L #K #V #W #U #i #l #_ #_ #_ #X #Y #H destruct
| #L #K #W #V #U #i #l #_ #_ #_ #X #Y #H destruct
| #I #L #V #T #U #l #_ #X #Y #H destruct
| #L #V #T #U #l #HTU #X #Y #H destruct /2 width=3/
| #L #V #W #T #U #l #_ #_ #X #Y #H destruct
]
qed.

(* Basic_1: was just: sty0_gen_appl *)
lemma ssta_inv_appl1: ∀h,g,L,Y,X,U,l. ⦃h, L⦄ ⊢ ⓐY.X •[g, l] U →
                      ∃∃Z. ⦃h, L⦄ ⊢ X •[g, l] Z & U = ⓐY.Z.
/2 width=3/ qed-.

fact ssta_inv_cast1_aux: ∀h,g,L,T,U,l. ⦃h, L⦄ ⊢ T •[g, l] U → ∀X,Y. T = ⓝY.X →
                         ∃∃Z1,Z2. ⦃h, L⦄ ⊢ Y •[g, l-1] Z1 & ⦃h, L⦄ ⊢ X •[g, l] Z2 &
                                  U = ⓝZ1.Z2.
#h #g #L #T #U #l * -L -T -U -l
[ #L #k #l #_ #X #Y #H destruct
| #L #K #V #W #U #l #i #_ #_ #_ #X #Y #H destruct
| #L #K #W #V #U #l #i #_ #_ #_ #X #Y #H destruct
| #I #L #V #T #U #l #_ #X #Y #H destruct
| #L #V #T #U #l #_ #X #Y #H destruct
| #L #V #W #T #U #l #HVW #HTU #X #Y #H destruct /2 width=5/
]
qed.

(* Basic_1: was just: sty0_gen_cast *)
lemma ssta_inv_cast1: ∀h,g,L,X,Y,U,l. ⦃h, L⦄ ⊢ ⓝY.X •[g, l] U →
                      ∃∃Z1,Z2. ⦃h, L⦄ ⊢ Y •[g, l-1] Z1 & ⦃h, L⦄ ⊢ X •[g, l] Z2 &
                               U = ⓝZ1.Z2.
/2 width=4/ qed-.