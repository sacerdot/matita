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

include "basic_2/unfold/sstas.ma".
include "basic_2/computation/cprs.ma".

(* DECOMPOSED EXTENDED PARALLEL COMPUTATION ON TERMS ************************)

definition dxprs: ∀h. sd h → lenv → relation term ≝ λh,g,L,T1,T2.
                  ∃∃T. ⦃h, L⦄ ⊢ T1 •*[g] T & L ⊢ T ➡* T2.

interpretation "decomposed extended parallel computation (term)"
   'DecomposedPRedStar h g L T1 T2 = (dxprs h g L T1 T2).

(* Basic properties *********************************************************)

lemma dxprs_refl: ∀h,g,L. reflexive … (dxprs h g L).
/2 width=3/ qed.

lemma sstas_dxprs: ∀h,g,L,T1,T2. ⦃h, L⦄ ⊢ T1 •*[g] T2 → ⦃h, L⦄ ⊢ T1 •*➡*[g] T2.
/2 width=3/ qed.

lemma cprs_dxprs: ∀h,g,L,T1,T2.  L ⊢ T1 ➡* T2 → ⦃h, L⦄ ⊢ T1 •*➡*[g] T2.
/2 width=3/ qed.

lemma dxprs_strap1: ∀h,g,L,T1,T,T2.
                    ⦃h, L⦄ ⊢ T1 •*➡*[g] T → L ⊢ T ➡ T2 → ⦃h, L⦄ ⊢ T1 •*➡*[g] T2.
#h #g #L #T1 #T #T2 * /3 width=5/
qed.

lemma dxprs_strap2: ∀h,g,L,T1,T,T2,l.
                    ⦃h, L⦄ ⊢ T1 •[g] ⦃l+1, T⦄ → ⦃h, L⦄ ⊢ T •*➡*[g] T2 → ⦃h, L⦄ ⊢ T1 •*➡*[g] T2.
#h #g #L #T1 #T #T2 #l #HT1 * /3 width=4/
qed.

lemma ssta_cprs_dxprs: ∀h,g,L,T1,T,T2,l. ⦃h, L⦄ ⊢ T1 •[g] ⦃l+1, T⦄ →
                       L ⊢ T ➡* T2 → ⦃h, L⦄ ⊢ T1 •*➡*[g] T2.
/3 width=3/ qed.

(* Basic inversion lemmas ***************************************************)

lemma dxprs_inv_abst1: ∀h,g,a,L,V1,T1,U2. ⦃h, L⦄ ⊢ ⓛ{a}V1. T1 •*➡*[g] U2 →
                       ∃∃V2,T2. L ⊢ V1 ➡* V2 & ⦃h, L.ⓛV1⦄ ⊢ T1 •*➡*[g] T2 &
                                U2 = ⓛ{a}V2. T2.
#h #g #a #L #V1 #T1 #U2 * #X #H1 #H2
elim (sstas_inv_bind1 … H1) -H1 #U #HTU1 #H destruct
elim (cprs_fwd_abst1 … H2 Abst V1) -H2 #V2 #T2 #HV12 #HUT2 #H destruct /3 width=5/
qed-.
