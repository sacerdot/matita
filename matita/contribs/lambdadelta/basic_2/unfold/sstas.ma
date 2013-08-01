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

include "basic_2/notation/relations/statictypestar_5.ma".
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
                    ∀U1,U2,l. ⦃G, L⦄ ⊢ T •* [h, g] U1 →  ⦃G, L⦄ ⊢ U1 •[h, g] ⦃l+1, U2⦄ →
                    R U1 → R U2
                 ) →
                 ∀U. ⦃G, L⦄ ⊢ T •*[h, g] U → R U.
#h #g #L #T #R #IH1 #IH2 #U #H elim H -U //
#U1 #U2 #H * /2 width=5/
qed-.

lemma sstas_ind_dx: ∀h,g,L,U2. ∀R:predicate term.
                    R U2 → (
                       ∀T,U1,l. ⦃G, L⦄ ⊢ T •[h, g] ⦃l+1, U1⦄ → ⦃G, L⦄ ⊢ U1 •* [h, g] U2 →
                       R U1 → R T
                    ) →
                    ∀T. ⦃G, L⦄ ⊢ T •*[h, g] U2 → R T.
#h #g #L #U2 #R #IH1 #IH2 #T #H @(star_ind_l … T H) -T //
#T #T0 * /2 width=5/
qed-.

(* Basic properties *********************************************************)

lemma sstas_refl: ∀h,g,L. reflexive … (sstas h g L).
// qed.

lemma ssta_sstas: ∀h,g,L,T,U,l. ⦃G, L⦄ ⊢ T •[h, g] ⦃l+1, U⦄ → ⦃G, L⦄ ⊢ T •*[h, g] U.
/3 width=2 by R_to_star, ex_intro/ qed. (**) (* auto fails without trace *)

lemma sstas_strap1: ∀h,g,L,T1,T2,U2,l. ⦃G, L⦄ ⊢ T1 •*[h, g] T2 → ⦃G, L⦄ ⊢ T2 •[h, g] ⦃l+1, U2⦄ →
                    ⦃G, L⦄ ⊢ T1 •*[h, g] U2.
/3 width=4 by sstep, ex_intro/ (**) (* auto fails without trace *)
qed.

lemma sstas_strap2: ∀h,g,L,T1,U1,U2,l. ⦃G, L⦄ ⊢ T1 •[h, g] ⦃l+1, U1⦄ → ⦃G, L⦄ ⊢ U1 •*[h, g] U2 →
                    ⦃G, L⦄ ⊢ T1 •*[h, g] U2.
/3 width=3 by star_compl, ex_intro/ (**) (* auto fails without trace *)
qed.

(* Basic inversion lemmas ***************************************************)

lemma sstas_inv_bind1: ∀h,g,a,I,L,Y,X,U. ⦃G, L⦄ ⊢ ⓑ{a,I}Y.X •*[h, g] U →
                       ∃∃Z. ⦃h, L.ⓑ{I}Y⦄ ⊢ X •*[h, g] Z & U = ⓑ{a,I}Y.Z.
#h #g #a #I #L #Y #X #U #H @(sstas_ind … H) -U /2 width=3/
#T #U #l #_ #HTU * #Z #HXZ #H destruct
elim (ssta_inv_bind1 … HTU) -HTU #Z0 #HZ0 #H destruct /3 width=4/
qed-.

lemma sstas_inv_appl1: ∀h,g,L,Y,X,U. ⦃G, L⦄ ⊢ ⓐY.X •*[h, g] U →
                       ∃∃Z. ⦃G, L⦄ ⊢ X •*[h, g] Z & U = ⓐY.Z.
#h #g #L #Y #X #U #H @(sstas_ind … H) -U /2 width=3/
#T #U #l #_ #HTU * #Z #HXZ #H destruct
elim (ssta_inv_appl1 … HTU) -HTU #Z0 #HZ0 #H destruct /3 width=4/
qed-.
