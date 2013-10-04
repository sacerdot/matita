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

include "basic_2/notation/relations/dpredstar_6.ma".
include "basic_2/unfold/lsstas.ma".
include "basic_2/computation/cprs.ma".

(* DECOMPOSED EXTENDED PARALLEL COMPUTATION ON TERMS ************************)

definition cpds: ∀h. sd h → relation4 genv lenv term term ≝
                 λh,g,G,L,T1,T2.
                 ∃∃T,l1,l2. l2 ≤ l1 & ⦃G, L⦄ ⊢ T1 ▪[h, g] l1 & ⦃G, L⦄ ⊢ T1 •*[h, g, l2] T & ⦃G, L⦄ ⊢ T ➡* T2.

interpretation "decomposed extended parallel computation (term)"
   'DPRedStar h g G L T1 T2 = (cpds h g G L T1 T2).

(* Basic properties *********************************************************)

lemma ssta_cprs_cpds: ∀h,g,G,L,T1,T,T2,l. ⦃G, L⦄ ⊢ T1 ▪[h, g] l+1 → ⦃G, L⦄ ⊢ T1 •[h, g] T →
                      ⦃G, L⦄ ⊢ T ➡* T2 → ⦃G, L⦄ ⊢ T1 •*➡*[h, g] T2.
/3 width=7/ qed.

lemma lsstas_cpds: ∀h,g,G,L,T1,T2,l. ⦃G, L⦄ ⊢ T1 ▪[h, g] l → ⦃G, L⦄ ⊢ T1 •*[h, g, l] T2 → ⦃G, L⦄ ⊢ T1 •*➡*[h, g] T2.
/2 width=7/ qed.

lemma cprs_cpds: ∀h,g,G,L,T1,T2,l.  ⦃G, L⦄ ⊢ T1 ▪[h, g] l → ⦃G, L⦄ ⊢ T1 ➡* T2 → ⦃G, L⦄ ⊢ T1 •*➡*[h, g] T2.
/2 width=7/ qed.

lemma cpds_refl: ∀h,g,G,L,T,l. ⦃G, L⦄ ⊢ T ▪[h, g] l → ⦃G, L⦄ ⊢ T •*➡*[h, g] T.
/2 width=2/ qed.

lemma cpds_strap1: ∀h,g,G,L,T1,T,T2.
                   ⦃G, L⦄ ⊢ T1 •*➡*[h, g] T → ⦃G, L⦄ ⊢ T ➡ T2 → ⦃G, L⦄ ⊢ T1 •*➡*[h, g] T2.
#h #g #G #L #T1 #T #T2 * /3 width=9/
qed.
