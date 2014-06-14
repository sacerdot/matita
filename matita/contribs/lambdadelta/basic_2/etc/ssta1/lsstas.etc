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

include "basic_2/notation/relations/statictypestar_7.ma".
include "basic_2/static/ssta.ma".

(* NAT-ITERATED STRATIFIED STATIC TYPE ASSIGNMENT FOR TERMS *****************)

definition lsstas: ∀h. sd h → genv → lenv → nat → relation term ≝
                   λh,g,G,L. lstar … (ssta h g G L).

interpretation "nat-iterated stratified static type assignment (term)"
   'StaticTypeStar h g G L l T U = (lsstas h g G L l T U).

(* Basic eliminators ********************************************************)

lemma lsstas_ind_sn: ∀h,g,G,L,U2. ∀R:relation2 nat term.
                     R 0 U2 → (
                        ∀l,T,U1. ⦃G, L⦄ ⊢ T •[h, g] U1 → ⦃G, L⦄ ⊢ U1 •* [h, g, l] U2 →
                        R l U1 → R (l+1) T
                     ) →
                     ∀l,T. ⦃G, L⦄ ⊢ T •*[h, g, l] U2 → R l T.
/3 width=5 by lstar_ind_l/ qed-.

lemma lsstas_ind_dx: ∀h,g,G,L,T. ∀R:relation2 nat term.
                     R 0 T → (
                        ∀l,U1,U2. ⦃G, L⦄ ⊢ T •* [h, g, l] U1 →  ⦃G, L⦄ ⊢ U1 •[h, g] U2 →
                        R l U1 → R (l+1) U2
                     ) →
                     ∀l,U. ⦃G, L⦄ ⊢ T •*[h, g, l] U → R l U.
/3 width=5 by lstar_ind_r/ qed-.

(* Basic inversion lemmas ***************************************************)

lemma lsstas_inv_O: ∀h,g,G,L,T,U. ⦃G, L⦄ ⊢ T •*[h, g, 0] U → T = U.
/2 width=4 by lstar_inv_O/ qed-.

lemma lsstas_inv_SO: ∀h,g,G,L,T,U. ⦃G, L⦄ ⊢ T •*[h, g, 1] U → ⦃G, L⦄ ⊢ T •[h, g] U.
/2 width=1 by lstar_inv_step/ qed-.

lemma lsstas_inv_step_sn: ∀h,g,G,L,T1,T2,l. ⦃G, L⦄ ⊢ T1 •*[h, g, l+1] T2 →
                         ∃∃T. ⦃G, L⦄ ⊢ T1 •[h, g] T & ⦃G, L⦄ ⊢ T •*[h, g, l] T2.
/2 width=3 by lstar_inv_S/ qed-.

lemma lsstas_inv_step_dx: ∀h,g,G,L,T1,T2,l. ⦃G, L⦄ ⊢ T1 •*[h, g, l+1] T2 →
                          ∃∃T. ⦃G, L⦄ ⊢ T1 •*[h, g, l] T & ⦃G, L⦄ ⊢ T •[h, g] T2.
/2 width=3 by lstar_inv_S_dx/ qed-.

lemma lsstas_inv_sort1: ∀h,g,G,L,X,k,l. ⦃G, L⦄ ⊢ ⋆k •*[h, g, l] X → X = ⋆((next h)^l k).
#h #g #G #L #X #k #l #H @(lsstas_ind_dx … H) -X -l //
#l #X #X0 #_ #H #IHX destruct
lapply (ssta_inv_sort1 … H) -H #H destruct
>iter_SO //
qed-.

lemma lsstas_inv_gref1: ∀h,g,G,L,X,p,l. ⦃G, L⦄ ⊢ §p •*[h, g, l+1] X → ⊥.
#h #g #G #L #X #p #l #H elim (lsstas_inv_step_sn … H) -H
#U #H #HUX elim (ssta_inv_gref1 … H)
qed-.

lemma lsstas_inv_bind1: ∀h,g,a,I,G,L,V,T,X,l. ⦃G, L⦄ ⊢ ⓑ{a,I}V.T •*[h, g, l] X →
                        ∃∃U. ⦃G, L.ⓑ{I}V⦄ ⊢ T •*[h, g, l] U & X = ⓑ{a,I}V.U.
#h #g #a #I #G #L #V #T #X #l #H @(lsstas_ind_dx … H) -X -l [ /2 width=3/ ]
#l #X #X0 #_ #HX0 * #U #HTU #H destruct
elim (ssta_inv_bind1 … HX0) -HX0 #U0 #HU0 #H destruct /3 width=3/
qed-.

lemma lsstas_inv_appl1: ∀h,g,G,L,V,T,X,l. ⦃G, L⦄ ⊢ ⓐV.T •*[h, g, l] X →
                        ∃∃U. ⦃G, L⦄ ⊢ T •*[h, g, l] U & X = ⓐV.U.
#h #g #G #L #V #T #X #l #H @(lsstas_ind_dx … H) -X -l [ /2 width=3/ ]
#l #X #X0 #_ #HX0 * #U #HTU #H destruct
elim (ssta_inv_appl1 … HX0) -HX0 #U0 #HU0 #H destruct /3 width=3/
qed-.

lemma lsstas_inv_cast1: ∀h,g,G,L,W,T,U,l. ⦃G, L⦄ ⊢ ⓝW.T •*[h, g, l+1] U → ⦃G, L⦄ ⊢ T •*[h, g, l+1] U.
#h #g #G #L #W #T #X #l #H elim (lsstas_inv_step_sn … H) -H
#U #H #HUX lapply (ssta_inv_cast1 … H) -H /2 width=3/
qed-.

(* Basic properties *********************************************************)

lemma lsstas_refl: ∀h,g,G,L. reflexive … (lsstas h g G L 0).
// qed.

lemma ssta_lsstas: ∀h,g,G,L,T,U. ⦃G, L⦄ ⊢ T •[h, g] U → ⦃G, L⦄ ⊢ T •*[h, g, 1] U.
/2 width=1/ qed.

lemma lsstas_step_sn: ∀h,g,G,L,T1,U1,U2,l. ⦃G, L⦄ ⊢ T1 •[h, g] U1 → ⦃G, L⦄ ⊢ U1 •*[h, g, l] U2 →
                      ⦃G, L⦄ ⊢ T1 •*[h, g, l+1] U2.
/2 width=3/ qed.

lemma lsstas_step_dx: ∀h,g,G,L,T1,T2,U2,l. ⦃G, L⦄ ⊢ T1 •*[h, g, l] T2 → ⦃G, L⦄ ⊢ T2 •[h, g] U2 →
                      ⦃G, L⦄ ⊢ T1 •*[h, g, l+1] U2.
/2 width=3/ qed.

lemma lsstas_split: ∀h,g,G,L. inv_ltransitive … (lsstas h g G L).
/2 width=1 by lstar_inv_ltransitive/ qed-.

lemma lsstas_sort: ∀h,g,G,L,l,k. ⦃G, L⦄ ⊢ ⋆k •*[h, g, l] ⋆((next h)^l k).
#h #g #G #L #l @(nat_ind_plus … l) -l //
#l #IHl #k >iter_SO /2 width=3/
qed.

lemma lsstas_bind: ∀h,g,I,G,L,V,T,U,l. ⦃G, L.ⓑ{I}V⦄ ⊢ T •*[h, g, l] U →
                   ∀a. ⦃G, L⦄ ⊢ ⓑ{a,I}V.T •*[h, g, l] ⓑ{a,I}V.U.
#h #g #I #G #L #V #T #U #l #H @(lsstas_ind_dx … H) -U -l // /3 width=3/
qed.

lemma lsstas_appl: ∀h,g,G,L,T,U,l. ⦃G, L⦄ ⊢ T •*[h, g, l] U →
                   ∀V.⦃G, L⦄ ⊢ ⓐV.T •*[h, g, l] ⓐV.U.
#h #g #G #L #T #U #l #H @(lsstas_ind_dx … H) -U -l // /3 width=3/
qed.

lemma lsstas_cast: ∀h,g,G,L,T,U,l. ⦃G, L⦄ ⊢ T •*[h, g, l+1] U →
                   ∀W. ⦃G, L⦄ ⊢ ⓝW.T •*[h, g, l+1] U.
#h #g #G #L #T #U #l #H elim (lsstas_inv_step_sn … H) -H /3 width=3/
qed.

(* Basic_1: removed theorems 7:
            sty1_abbr sty1_appl sty1_bind sty1_cast2
            sty1_correct sty1_lift sty1_trans
*)
