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

include "basic_2/static/ssta.ma".

(* ITERATED STRATIFIED STATIC TYPE ASSIGNMENT FOR TERMS *********************)

inductive sstas (h:sh) (g:sd h) (L:lenv): relation term ≝
| sstas_refl: ∀T,U,l. ⦃h, L⦄ ⊢ T •[g, l] U → sstas h g L T T
| sstas_step: ∀T,U1,U2,l. ⦃h, L⦄ ⊢ T •[g, l+1] U1 → sstas h g L U1 U2 →
              sstas h g L T U2.

interpretation "iterated stratified static type assignment (term)"
   'StaticTypeStar h g L T U = (sstas h g L T U).

(* Basic eliminators ********************************************************)

fact sstas_ind_alt_aux: ∀h,g,L,U2. ∀R:predicate term.
                        (∀T,l. ⦃h, L⦄ ⊢ U2 •[g , l] T → R U2) →
                        (∀T,U1,l. ⦃h, L⦄ ⊢ T •[g, l + 1] U1 →
                                  ⦃h, L⦄ ⊢ U1 •* [g] U2 → R U1 → R T
                        ) →
                        ∀T,U. ⦃h, L⦄ ⊢ T •*[g] U → U = U2 → R T.
#h #g #L #U2 #R #H1 #H2 #T #U #H elim H -H -T -U /2 width=3/ /3 width=5/
qed-.

lemma sstas_ind_alt: ∀h,g,L,U2. ∀R:predicate term.
                     (∀T,l. ⦃h, L⦄ ⊢ U2 •[g , l] T → R U2) →
                     (∀T,U1,l. ⦃h, L⦄ ⊢ T •[g, l + 1] U1 →
                               ⦃h, L⦄ ⊢ U1 •* [g] U2 → R U1 → R T
                     ) →
                     ∀T. ⦃h, L⦄ ⊢ T •*[g] U2 → R T.
/3 width=9 by sstas_ind_alt_aux/ qed-.
                         
(* Basic inversion lemmas ***************************************************)

fact sstas_inv_bind1_aux: ∀h,g,L,T,U. ⦃h, L⦄ ⊢ T •*[g] U →
                          ∀a,J,X,Y. T = ⓑ{a,J}Y.X →
                          ∃∃Z. ⦃h, L.ⓑ{J}Y⦄ ⊢ X •*[g] Z & U = ⓑ{a,J}Y.Z.
#h #g #L #T #U #H @(sstas_ind_alt … H) -T
[ #U0 #l #HU0 #a #J #X #Y #H destruct
  elim (ssta_inv_bind1 … HU0) -HU0 #X0 #HX0 #H destruct /3 width=3/
| #T0 #U0 #l #HTU0 #_ #IHU0 #a #J #X #Y #H destruct
  elim (ssta_inv_bind1 … HTU0) -HTU0 #X0 #HX0 #H destruct
  elim (IHU0 a J X0 Y …) -IHU0 // #X1 #HX01 #H destruct /3 width=4/
]
qed-.

lemma sstas_inv_bind1: ∀h,g,a,J,L,Y,X,U. ⦃h, L⦄ ⊢ ⓑ{a,J}Y.X •*[g] U →
                       ∃∃Z. ⦃h, L.ⓑ{J}Y⦄ ⊢ X •*[g] Z & U = ⓑ{a,J}Y.Z.
/2 width=3 by sstas_inv_bind1_aux/ qed-.

fact sstas_inv_appl1_aux: ∀h,g,L,T,U. ⦃h, L⦄ ⊢ T •*[g] U → ∀X,Y. T = ⓐY.X →
                          ∃∃Z. ⦃h, L⦄ ⊢ X •*[g] Z & U = ⓐY.Z.
#h #g #L #T #U #H @(sstas_ind_alt … H) -T
[ #U0 #l #HU0 #X #Y #H destruct
  elim (ssta_inv_appl1 … HU0) -HU0 #X0 #HX0 #H destruct /3 width=3/
| #T0 #U0 #l #HTU0 #_ #IHU0 #X #Y #H destruct
  elim (ssta_inv_appl1 … HTU0) -HTU0 #X0 #HX0 #H destruct
  elim (IHU0 X0 Y ?) -IHU0 // #X1 #HX01 #H destruct /3 width=4/
]
qed-.

lemma sstas_inv_appl1: ∀h,g,L,Y,X,U. ⦃h, L⦄ ⊢ ⓐY.X •*[g] U →
                       ∃∃Z. ⦃h, L⦄ ⊢ X •*[g] Z & U = ⓐY.Z.
/2 width=3 by sstas_inv_appl1_aux/ qed-.

(* Basic forward lemmas *****************************************************)

lemma sstas_fwd_correct: ∀h,g,L,T,U. ⦃h, L⦄ ⊢ T •*[g] U →
                         ∃∃l,W. ⦃h, L⦄ ⊢ U •[g, l] W.
#h #g #L #T #U #H @(sstas_ind_alt … H) -T // /2 width=3/
qed-.
