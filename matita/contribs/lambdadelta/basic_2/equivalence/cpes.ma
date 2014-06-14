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

include "basic_2/notation/relations/dpconvstar_6.ma".
include "basic_2/static/da.ma".
include "basic_2/unfold/lstas.ma".
include "basic_2/equivalence/cpcs.ma".

(* DECOMPOSED EXTENDED PARALLEL EQUIVALENCE FOR TERMS ***********************)

definition cpes: ∀h. sd h → relation4 genv lenv term term ≝
                 λh,g,G,L,T1,T2.
                 ∃∃T,l1,l2. l2 ≤ l1 & ⦃G, L⦄ ⊢ T1 ▪[h, g] l1 & ⦃G, L⦄ ⊢ T1 •*[h, l2] T & ⦃G, L⦄ ⊢ T ⬌* T2.

interpretation "decomposed extended parallel equivalence (term)"
   'DPConvStar h g G L T1 T2 = (cpes h g G L T1 T2).

(* Basic properties *********************************************************)

lemma sta_cpcs_cpes: ∀h,g,G,L,T1,T,T2,l. ⦃G, L⦄ ⊢ T1 ▪[h, g] l+1 → ⦃G, L⦄ ⊢ T1 •[h] T →
                     ⦃G, L⦄ ⊢ T ⬌* T2 → ⦃G, L⦄ ⊢ T1 •*⬌*[h, g] T2.
/3 width=7 by sta_lstas, ex4_3_intro/ qed.

lemma lstas_cpes: ∀h,g,G,L,T1,T2,l. ⦃G, L⦄ ⊢ T1 ▪[h, g] l → ⦃G, L⦄ ⊢ T1 •*[h, l] T2 → ⦃G, L⦄ ⊢ T1 •*⬌*[h, g] T2.
/2 width=7 by ex4_3_intro/ qed.

lemma cpcs_cpes: ∀h,g,G,L,T1,T2,l.  ⦃G, L⦄ ⊢ T1 ▪[h, g] l → ⦃G, L⦄ ⊢ T1 ⬌* T2 → ⦃G, L⦄ ⊢ T1 •*⬌*[h, g] T2.
/2 width=7 by lstar_O, ex4_3_intro/ qed.

lemma cpes_refl: ∀h,g,G,L,T,l. ⦃G, L⦄ ⊢ T ▪[h, g] l → ⦃G, L⦄ ⊢ T •*⬌*[h, g] T.
/2 width=2 by cpcs_cpes/ qed.

lemma cpes_strap1: ∀h,g,G,L,T1,T,T2.
                   ⦃G, L⦄ ⊢ T1 •*⬌*[h, g] T → ⦃G, L⦄ ⊢ T ⬌ T2 → ⦃G, L⦄ ⊢ T1 •*⬌*[h, g] T2.
#h #g #G #L #T1 #T #T2 * /3 width=9 by cpcs_strap1, ex4_3_intro/
qed.
