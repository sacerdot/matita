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
include "basic_2/reducibility/cpr.ma".

(* EXTENDED PARALLEL REDUCTION ON TERMS *************************************)

definition xpr: ∀h. sd h → lenv → relation term ≝
   λh,g,L,T1,T2. L ⊢ T1 ➡ T2 ∨ ∃l. ⦃h, L⦄ ⊢ T1 •[g, l + 1] T2.

interpretation
   "extended parallel reduction (term)"
   'XPRed h g L T1 T2 = (xpr h g L T1 T2).

(* Basic properties *********************************************************)

lemma cpr_xpr: ∀h,g,L,T1,T2. L ⊢ T1 ➡ T2 → ⦃h, L⦄ ⊢ T1 ➸[g] T2.
/2 width=1/ qed.

lemma ssta_xpr: ∀h,g,L,T1,T2,l. ⦃h, L⦄ ⊢ T1 •[g, l + 1] T2 → ⦃h, L⦄ ⊢ T1 ➸[g] T2.
/3 width=2/ qed.

lemma xpr_refl: ∀h,g,L,T. ⦃h, L⦄ ⊢ T ➸[g] T.
/2 width=1/ qed.
