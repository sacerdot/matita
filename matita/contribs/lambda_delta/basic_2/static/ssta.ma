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
include "basic_2/unfold/frsups.ma".
include "basic_2/static/sd.ma".

(* STRATIFIED STATIC TYPE ASSIGNMENT ON TERMS *******************************)

inductive ssta (h:sh) (g:sd h): nat → lenv → relation term ≝
| ssta_sort: ∀L,k,l. deg h g k l → ssta h g l L (⋆k) (⋆(next h k))
| ssta_ldef: ∀L,K,V,W,U,i,l. ⇩[0, i] L ≡ K. ⓓV → ssta h g l K V W →
             ⇧[0, i + 1] W ≡ U → ssta h g l L (#i) U
| ssta_ldec: ∀L,K,W,V,U,i,l. ⇩[0, i] L ≡ K. ⓛW → ssta h g l K W V →
             ⇧[0, i + 1] W ≡ U → ssta h g (l+1) L (#i) U
| ssta_bind: ∀a,I,L,V,T,U,l. ssta h g l (L. ⓑ{I} V) T U →
             ssta h g l L (ⓑ{a,I}V.T) (ⓑ{a,I}V.U)
| ssta_appl: ∀L,V,T,U,l. ssta h g l L T U →
             ssta h g l L (ⓐV.T) (ⓐV.U)
| ssta_cast: ∀L,W,T,U,l. ssta h g l L T U → ssta h g l L (ⓝW. T) U
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
| #a #I #L #V #T #U #l #_ #k0 #H destruct
| #L #V #T #U #l #_ #k0 #H destruct
| #L #W #T #U #l #_ #k0 #H destruct
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
| #a #I #L #V #T #U #l #_ #j #H destruct
| #L #V #T #U #l #_ #j #H destruct
| #L #W #T #U #l #_ #j #H destruct
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
                         ∀a,I,X,Y. T = ⓑ{a,I}Y.X →
                         ∃∃Z. ⦃h, L.ⓑ{I}Y⦄ ⊢ X •[g, l] Z & U = ⓑ{a,I}Y.Z.
#h #g #L #T #U #l * -L -T -U -l
[ #L #k #l #_ #a #I #X #Y #H destruct
| #L #K #V #W #U #i #l #_ #_ #_ #a #I #X #Y #H destruct
| #L #K #W #V #U #i #l #_ #_ #_ #a #I #X #Y #H destruct
| #b #J #L #V #T #U #l #HTU #a #I #X #Y #H destruct /2 width=3/
| #L #V #T #U #l #_ #a #I #X #Y #H destruct
| #L #W #T #U #l #_ #a #I #X #Y #H destruct
]
qed.

(* Basic_1: was just: sty0_gen_bind *)
lemma ssta_inv_bind1: ∀h,g,a,I,L,Y,X,U,l. ⦃h, L⦄ ⊢ ⓑ{a,I}Y.X •[g, l] U →
                      ∃∃Z. ⦃h, L.ⓑ{I}Y⦄ ⊢ X •[g, l] Z & U = ⓑ{a,I}Y.Z.
/2 width=3/ qed-.

fact ssta_inv_appl1_aux: ∀h,g,L,T,U,l. ⦃h, L⦄ ⊢ T •[g, l] U → ∀X,Y. T = ⓐY.X →
                         ∃∃Z. ⦃h, L⦄ ⊢ X •[g, l] Z & U = ⓐY.Z.
#h #g #L #T #U #l * -L -T -U -l
[ #L #k #l #_ #X #Y #H destruct
| #L #K #V #W #U #i #l #_ #_ #_ #X #Y #H destruct
| #L #K #W #V #U #i #l #_ #_ #_ #X #Y #H destruct
| #a #I #L #V #T #U #l #_ #X #Y #H destruct
| #L #V #T #U #l #HTU #X #Y #H destruct /2 width=3/
| #L #W #T #U #l #_ #X #Y #H destruct
]
qed.

(* Basic_1: was just: sty0_gen_appl *)
lemma ssta_inv_appl1: ∀h,g,L,Y,X,U,l. ⦃h, L⦄ ⊢ ⓐY.X •[g, l] U →
                      ∃∃Z. ⦃h, L⦄ ⊢ X •[g, l] Z & U = ⓐY.Z.
/2 width=3/ qed-.

fact ssta_inv_cast1_aux: ∀h,g,L,T,U,l. ⦃h, L⦄ ⊢ T •[g, l] U →
                         ∀X,Y. T = ⓝY.X → ⦃h, L⦄ ⊢ X •[g, l] U.
#h #g #L #T #U #l * -L -T -U -l
[ #L #k #l #_ #X #Y #H destruct
| #L #K #V #W #U #l #i #_ #_ #_ #X #Y #H destruct
| #L #K #W #V #U #l #i #_ #_ #_ #X #Y #H destruct
| #a #I #L #V #T #U #l #_ #X #Y #H destruct
| #L #V #T #U #l #_ #X #Y #H destruct
| #L #W #T #U #l #HTU #X #Y #H destruct //
]
qed.

(* Basic_1: was just: sty0_gen_cast *)
lemma ssta_inv_cast1: ∀h,g,L,X,Y,U,l. ⦃h, L⦄ ⊢ ⓝY.X •[g, l] U →
                      ⦃h, L⦄ ⊢ X •[g, l] U.
/2 width=4/ qed-.

(* Advanced inversion lemmas ************************************************)

lemma ssta_inv_frsupp: ∀h,g,L,T,U,l. ⦃h, L⦄ ⊢ T •[g, l] U → ⦃L, U⦄ ⧁+ ⦃L, T⦄ → ⊥.
#h #g #L #T #U #l #H elim H -L -T -U -l
[ #L #k #l #_ #H
  elim (frsupp_inv_atom1_frsups … H)
| #L #K #V #W #U #i #l #_ #_ #HWU #_ #H
  elim (lift_frsupp_trans … (⋆) … H … HWU) -U #X #H
  elim (lift_inv_lref2_be … H ? ?) -H //
| #L #K #W #V #U #i #l #_ #_ #HWU #_ #H
  elim (lift_frsupp_trans … (⋆) … H … HWU) -U #X #H
  elim (lift_inv_lref2_be … H ? ?) -H //
| #a #I #L #V #T #U #l #_ #IHTU #H
  elim (frsupp_inv_bind1_frsups … H) -H #H [2: /4 width=4/ ] -IHTU
  lapply (frsups_fwd_fw … H) -H normalize
  <associative_plus <associative_plus #H
  elim (le_plus_xySz_x_false … H)
| #L #V #T #U #l #_ #IHTU #H
  elim (frsupp_inv_flat1_frsups … H) -H #H [2: /4 width=4/ ] -IHTU
  lapply (frsups_fwd_fw … H) -H normalize
  <associative_plus <associative_plus #H
  elim (le_plus_xySz_x_false … H)
| /3 width=4/
]
qed-.

fact ssta_inv_refl_aux: ∀h,g,L,T,U,l. ⦃h, L⦄ ⊢ T •[g, l] U → T = U → ⊥.
#h #g #L #T #U #l #H elim H -L -T -U -l
[ #L #k #l #_ #H
  lapply (next_lt h k) destruct -H -e0 (**) (* destruct: these premises are not erased *)
  <e1 -e1 #H elim (lt_refl_false … H)
| #L #K #V #W #U #i #l #_ #_ #HWU #_ #H destruct
  elim (lift_inv_lref2_be … HWU ? ?) -HWU //
| #L #K #W #V #U #i #l #_ #_ #HWU #_ #H destruct
  elim (lift_inv_lref2_be … HWU ? ?) -HWU //
| #a #I #L #V #T #U #l #_ #IHTU #H destruct /2 width=1/
| #L #V #T #U #l #_ #IHTU #H destruct /2 width=1/
| #L #W #T #U #l #HTU #_ #H destruct
  elim (ssta_inv_frsupp … HTU ?) -HTU /2 width=1/
]
qed-.

lemma ssta_inv_refl: ∀h,g,T,L,l. ⦃h, L⦄ ⊢ T •[g, l] T → ⊥.
/2 width=8 by ssta_inv_refl_aux/ qed-.

lemma ssta_inv_frsups: ∀h,g,L,T,U,l. ⦃h, L⦄ ⊢ T •[g, l] U → ⦃L, U⦄ ⧁* ⦃L, T⦄ → ⊥.
#h #g #L #T #U #L #HTU #H elim (frsups_inv_all … H) -H
[ * #_ #H destruct /2 width=6 by ssta_inv_refl/
| /2 width=8 by ssta_inv_frsupp/
]
qed-.
