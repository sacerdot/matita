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
include "basic_2/static/sta.ma".

(* NAT-ITERATED STATIC TYPE ASSIGNMENT FOR TERMS ****************************)

definition lstas: ∀h. genv → lenv → nat → relation term ≝
                  λh,G,L. lstar … (sta h G L).

interpretation "nat-iterated static type assignment (term)"
   'StaticTypeStar h G L l T U = (lstas h G L l T U).

(* Basic eliminators ********************************************************)

lemma lstas_ind_sn: ∀h,G,L,U2. ∀R:relation2 nat term.
                    R 0 U2 → (
                       ∀l,T,U1. ⦃G, L⦄ ⊢ T •[h] U1 → ⦃G, L⦄ ⊢ U1 •* [h, l] U2 →
                       R l U1 → R (l+1) T
                    ) →
                    ∀l,T. ⦃G, L⦄ ⊢ T •*[h, l] U2 → R l T.
/3 width=5 by lstar_ind_l/ qed-.

lemma lstas_ind_dx: ∀h,G,L,T. ∀R:relation2 nat term.
                    R 0 T → (
                       ∀l,U1,U2. ⦃G, L⦄ ⊢ T •* [h, l] U1 →  ⦃G, L⦄ ⊢ U1 •[h] U2 →
                       R l U1 → R (l+1) U2
                    ) →
                    ∀l,U. ⦃G, L⦄ ⊢ T •*[h, l] U → R l U.
/3 width=5 by lstar_ind_r/ qed-.

(* Basic inversion lemmas ***************************************************)

lemma lstas_inv_O: ∀h,G,L,T,U. ⦃G, L⦄ ⊢ T •*[h, 0] U → T = U.
/2 width=4 by lstar_inv_O/ qed-.

lemma lstas_inv_SO: ∀h,G,L,T,U. ⦃G, L⦄ ⊢ T •*[h, 1] U → ⦃G, L⦄ ⊢ T •[h] U.
/2 width=1 by lstar_inv_step/ qed-.

lemma lstas_inv_step_sn: ∀h,G,L,T1,T2,l. ⦃G, L⦄ ⊢ T1 •*[h, l+1] T2 →
                         ∃∃T. ⦃G, L⦄ ⊢ T1 •[h] T & ⦃G, L⦄ ⊢ T •*[h, l] T2.
/2 width=3 by lstar_inv_S/ qed-.

lemma lstas_inv_step_dx: ∀h,G,L,T1,T2,l. ⦃G, L⦄ ⊢ T1 •*[h, l+1] T2 →
                         ∃∃T. ⦃G, L⦄ ⊢ T1 •*[h, l] T & ⦃G, L⦄ ⊢ T •[h] T2.
/2 width=3 by lstar_inv_S_dx/ qed-.

lemma lstas_inv_sort1: ∀h,G,L,X,k,l. ⦃G, L⦄ ⊢ ⋆k •*[h, l] X → X = ⋆((next h)^l k).
#h #G #L #X #k #l #H @(lstas_ind_dx … H) -X -l //
#l #X #X0 #_ #H #IHX destruct
lapply (sta_inv_sort1 … H) -H #H destruct
>iter_SO //
qed-.

lemma lstas_inv_gref1: ∀h,G,L,X,p,l. ⦃G, L⦄ ⊢ §p •*[h, l+1] X → ⊥.
#h #G #L #X #p #l #H elim (lstas_inv_step_sn … H) -H
#U #H #HUX elim (sta_inv_gref1 … H)
qed-.

lemma lstas_inv_bind1: ∀h,a,I,G,L,V,T,X,l. ⦃G, L⦄ ⊢ ⓑ{a,I}V.T •*[h, l] X →
                       ∃∃U. ⦃G, L.ⓑ{I}V⦄ ⊢ T •*[h, l] U & X = ⓑ{a,I}V.U.
#h #a #I #G #L #V #T #X #l #H @(lstas_ind_dx … H) -X -l /2 width=3 by ex2_intro/
#l #X #X0 #_ #HX0 * #U #HTU #H destruct
elim (sta_inv_bind1 … HX0) -HX0 #U0 #HU0 #H destruct /3 width=3 by lstar_dx, ex2_intro/
qed-.

lemma lstas_inv_appl1: ∀h,G,L,V,T,X,l. ⦃G, L⦄ ⊢ ⓐV.T •*[h, l] X →
                       ∃∃U. ⦃G, L⦄ ⊢ T •*[h, l] U & X = ⓐV.U.
#h #G #L #V #T #X #l #H @(lstas_ind_dx … H) -X -l /2 width=3 by ex2_intro/
#l #X #X0 #_ #HX0 * #U #HTU #H destruct
elim (sta_inv_appl1 … HX0) -HX0 #U0 #HU0 #H destruct /3 width=3 by lstar_dx, ex2_intro/
qed-.

lemma lstas_inv_cast1: ∀h,G,L,W,T,U,l. ⦃G, L⦄ ⊢ ⓝW.T •*[h, l+1] U → ⦃G, L⦄ ⊢ T •*[h, l+1] U.
#h #G #L #W #T #X #l #H elim (lstas_inv_step_sn … H) -H
#U #H #HUX lapply (sta_inv_cast1 … H) -H /2 width=3 by lstar_S/
qed-.

(* Basic properties *********************************************************)

lemma lstas_refl: ∀h,G,L. reflexive … (lstas h G L 0).
// qed.

lemma sta_lstas: ∀h,G,L,T,U. ⦃G, L⦄ ⊢ T •[h] U → ⦃G, L⦄ ⊢ T •*[h, 1] U.
/2 width=1 by lstar_step/ qed.

lemma lstas_step_sn: ∀h,G,L,T1,U1,U2,l. ⦃G, L⦄ ⊢ T1 •[h] U1 → ⦃G, L⦄ ⊢ U1 •*[h, l] U2 →
                     ⦃G, L⦄ ⊢ T1 •*[h, l+1] U2.
/2 width=3 by lstar_S/ qed.

lemma lstas_step_dx: ∀h,G,L,T1,T2,U2,l. ⦃G, L⦄ ⊢ T1 •*[h, l] T2 → ⦃G, L⦄ ⊢ T2 •[h] U2 →
                     ⦃G, L⦄ ⊢ T1 •*[h, l+1] U2.
/2 width=3 by lstar_dx/ qed.

lemma lstas_split: ∀h,G,L. inv_ltransitive … (lstas h G L).
/2 width=1 by lstar_inv_ltransitive/ qed-.

lemma lstas_sort: ∀h,G,L,l,k. ⦃G, L⦄ ⊢ ⋆k •*[h, l] ⋆((next h)^l k).
#h #G #L #l @(nat_ind_plus … l) -l //
#l #IHl #k >iter_SO /2 width=3 by sta_sort, lstas_step_dx/
qed.

lemma lstas_bind: ∀h,I,G,L,V,T,U,l. ⦃G, L.ⓑ{I}V⦄ ⊢ T •*[h, l] U →
                  ∀a. ⦃G, L⦄ ⊢ ⓑ{a,I}V.T •*[h, l] ⓑ{a,I}V.U.
#h #I #G #L #V #T #U #l #H @(lstas_ind_dx … H) -U -l /3 width=3 by sta_bind, lstar_O, lstas_step_dx/
qed.

lemma lstas_appl: ∀h,G,L,T,U,l. ⦃G, L⦄ ⊢ T •*[h, l] U →
                  ∀V.⦃G, L⦄ ⊢ ⓐV.T •*[h, l] ⓐV.U.
#h #G #L #T #U #l #H @(lstas_ind_dx … H) -U -l /3 width=3 by sta_appl, lstar_O, lstas_step_dx/
qed.

lemma lstas_cast: ∀h,G,L,T,U,l. ⦃G, L⦄ ⊢ T •*[h, l+1] U →
                  ∀W. ⦃G, L⦄ ⊢ ⓝW.T •*[h, l+1] U.
#h #G #L #T #U #l #H elim (lstas_inv_step_sn … H) -H /3 width=3 by sta_cast, lstas_step_sn/
qed.

(* Basic_1: removed theorems 7:
            sty1_abbr sty1_appl sty1_bind sty1_cast2
            sty1_correct sty1_lift sty1_trans
*)
