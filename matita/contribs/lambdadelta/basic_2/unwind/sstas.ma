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

(* Note: includes: stass_refl *)
definition sstas: ∀h. sd h → lenv → relation term ≝
                  λh,g,L. star … (ssta_step h g L).

interpretation "iterated stratified static type assignment (term)"
   'StaticTypeStar h g L T U = (sstas h g L T U).

(* Basic eliminators ********************************************************)

lemma sstas_ind: ∀h,g,L,T. ∀R:predicate term.
                 R T → (
                    ∀U1,U2,l. ⦃h, L⦄ ⊢ T •* [g] U1 →  ⦃h, L⦄ ⊢ U1 •[g, l + 1] U2 →
                    R U1 → R U2
                 ) →
                 ∀U. ⦃h, L⦄ ⊢ T •*[g] U → R U.
#h #g #L #T #R #IH1 #IH2 #U #H elim H -U //
#U1 #U2 #H * /2 width=5/
qed-.

lemma sstas_ind_dx: ∀h,g,L,U2. ∀R:predicate term.
                    R U2 → (
                       ∀T,U1,l. ⦃h, L⦄ ⊢ T •[g, l + 1] U1 → ⦃h, L⦄ ⊢ U1 •* [g] U2 →
                       R U1 → R T
                    ) →
                    ∀T. ⦃h, L⦄ ⊢ T •*[g] U2 → R T.
#h #g #L #U2 #R #IH1 #IH2 #T #H @(star_ind_l … T H) -T //
#T #T0 * /2 width=5/
qed-.

(* Basic properties *********************************************************)

lemma ssta_sstas: ∀h,g,L,T,U,l. ⦃h, L⦄ ⊢ T •[g, l+1] U → ⦃h, L⦄ ⊢ T •*[g] U.
/3 width=2 by R_to_star, ex_intro/ qed. (**) (* auto fails without trace *)

lemma sstas_strap1: ∀h,g,L,T1,T2,U2,l. ⦃h, L⦄ ⊢ T1 •*[g] T2 → ⦃h, L⦄ ⊢ T2 •[g,l+1] U2 →
                    ⦃h, L⦄ ⊢ T1 •*[g] U2.
/3 width=4 by sstep, ex_intro/ (**) (* auto fails without trace *)
qed.

lemma sstas_strap2: ∀h,g,L,T1,U1,U2,l. ⦃h, L⦄ ⊢ T1 •[g, l+1] U1 → ⦃h, L⦄ ⊢ U1 •*[g] U2 →
                    ⦃h, L⦄ ⊢ T1 •*[g] U2.
/3 width=3 by star_compl, ex_intro/ (**) (* auto fails without trace *)
qed.

(* Basic inversion lemmas ***************************************************)

lemma sstas_inv_bind1: ∀h,g,a,I,L,Y,X,U. ⦃h, L⦄ ⊢ ⓑ{a,I}Y.X •*[g] U →
                       ∃∃Z. ⦃h, L.ⓑ{I}Y⦄ ⊢ X •*[g] Z & U = ⓑ{a,I}Y.Z.
#h #g #a #I #L #Y #X #U #H @(sstas_ind … H) -U /2 width=3/
#T #U #l #_ #HTU * #Z #HXZ #H destruct
elim (ssta_inv_bind1 … HTU) -HTU #Z0 #HZ0 #H destruct /3 width=4/
qed-.

lemma sstas_inv_appl1: ∀h,g,L,Y,X,U. ⦃h, L⦄ ⊢ ⓐY.X •*[g] U →
                       ∃∃Z. ⦃h, L⦄ ⊢ X •*[g] Z & U = ⓐY.Z.
#h #g #L #Y #X #U #H @(sstas_ind … H) -U /2 width=3/
#T #U #l #_ #HTU * #Z #HXZ #H destruct
elim (ssta_inv_appl1 … HTU) -HTU #Z0 #HZ0 #H destruct /3 width=4/
qed-.
