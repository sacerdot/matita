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

include "explicit_updating/syntax/substitution_unwind.ma".
include "explicit_updating/syntax/substitution_tapp.ma".
include "explicit_updating/notation/functions/black_downtriangle_2.ma".

(* UNWIND FOR TERM *********************************************************)

definition unwind (f): 𝕋 → 𝕋 ≝
           subst_tapp (subst_unwind f)
.

interpretation
  "unwind (term)"
  'BlackDownTriangle f t = (unwind f t).

(* Basic constructions ******************************************************)

lemma unwind_unfold (f) (t):
      (𝐬❨f❩＠⧣❨t❩) = ▼[f]t.
//
qed.

lemma unwind_lref (f) (p):
      ξ(f＠⧣❨p❩) = ▼[f](ξp).
#f #p
//
qed.

lemma unwind_appl (f) (v) (t):
      (＠▼[f]v.▼[f]t) = ▼[f](＠v.t).
#f #v #t
//
qed.
