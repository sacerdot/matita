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

include "basic_2/notation/relations/dpredstar_5.ma".
include "basic_2/unfold/sstas.ma".
include "basic_2/computation/cprs.ma".

(* DECOMPOSED EXTENDED PARALLEL COMPUTATION ON TERMS ************************)

definition cpds: ∀h. sd h → lenv → relation term ≝ λh,g,L,T1,T2.
                 ∃∃T. ⦃h, L⦄ ⊢ T1 •*[g] T & L ⊢ T ➡* T2.

interpretation "decomposed extended parallel computation (term)"
   'DPRedStar h g L T1 T2 = (cpds h g L T1 T2).

(* Basic properties *********************************************************)

lemma cpds_refl: ∀h,g,L. reflexive … (cpds h g L).
/2 width=3/ qed.

lemma sstas_cpds: ∀h,g,L,T1,T2. ⦃h, L⦄ ⊢ T1 •*[g] T2 → ⦃h, L⦄ ⊢ T1 •*➡*[g] T2.
/2 width=3/ qed.

lemma cprs_cpds: ∀h,g,L,T1,T2.  L ⊢ T1 ➡* T2 → ⦃h, L⦄ ⊢ T1 •*➡*[g] T2.
/2 width=3/ qed.

lemma cpds_strap1: ∀h,g,L,T1,T,T2.
                   ⦃h, L⦄ ⊢ T1 •*➡*[g] T → L ⊢ T ➡ T2 → ⦃h, L⦄ ⊢ T1 •*➡*[g] T2.
#h #g #L #T1 #T #T2 * /3 width=5/
qed.

lemma cpds_strap2: ∀h,g,L,T1,T,T2,l.
                   ⦃h, L⦄ ⊢ T1 •[g] ⦃l+1, T⦄ → ⦃h, L⦄ ⊢ T •*➡*[g] T2 → ⦃h, L⦄ ⊢ T1 •*➡*[g] T2.
#h #g #L #T1 #T #T2 #l #HT1 * /3 width=4/
qed.

lemma ssta_cprs_cpds: ∀h,g,L,T1,T,T2,l. ⦃h, L⦄ ⊢ T1 •[g] ⦃l+1, T⦄ →
                      L ⊢ T ➡* T2 → ⦃h, L⦄ ⊢ T1 •*➡*[g] T2.
/3 width=3/ qed.
