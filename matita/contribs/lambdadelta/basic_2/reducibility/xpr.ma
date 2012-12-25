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

inductive xpr (h) (g) (L) (T1) (T2): Prop ≝
| xpr_cpr : L ⊢ T1 ➡ T2 → xpr h g L T1 T2
| xpr_ssta: ∀l. ⦃h, L⦄ ⊢ T1 •[g, l + 1] T2 → xpr h g L T1 T2
.

interpretation
   "extended parallel reduction (term)"
   'XPRed h g L T1 T2 = (xpr h g L T1 T2).

(* Basic properties *********************************************************)

lemma xpr_refl: ∀h,g,L. reflexive … (xpr h g L).
/2 width=1/ qed.