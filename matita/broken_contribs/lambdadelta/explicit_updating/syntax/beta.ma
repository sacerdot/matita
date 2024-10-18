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

include "explicit_updating/syntax/substitution_beta.ma".
include "explicit_updating/syntax/substitution_pushs.ma".
include "explicit_updating/syntax/substitution_tapp.ma".
include "explicit_updating/notation/functions/square_sw_black_3.ma".

(* β-SUBSTITUTION FOR TERM **************************************************)

definition beta (n) (v): 𝕋 → 𝕋 ≝
           subst_tapp (⫯*[n]𝐬❨v❩)
.

interpretation
  "β-substitution (term)"
  'SquareSWBlack n v t = (beta n v t).

(* Basic constructions ******************************************************)

lemma beta_unfold (n) (v) (t):
      (⫯*[n]𝐬❨v❩＠⧣❨t❩) = ⬕[n←v]t.
//
qed.

lemma beta_zero_lref_unit (v):
      v = ⬕[𝟎←v]ξ𝟏.
//
qed.

lemma beta_zero_lref_succ (v) (p):
      ξp = ⬕[𝟎←v]ξ↑p.
//
qed.

lemma beta_succ_lref_unit (n:ℕ) (v):
      (ξ𝟏) = ⬕[⁤↑n←v]ξ𝟏.
#n #v
<beta_unfold //
qed.

lemma beta_abst (b) (n) (v) (t):
      (𝛌b.⬕[⁤↑n←v]t) = ⬕[n←v](𝛌b.t).
#b #n #v #t
<beta_unfold <beta_unfold
<subst_tapp_abst <subst_pushs_succ //
qed.

lemma beta_appl (n) (w) (v) (t):
      (＠(⬕[n←w]v).⬕[n←w]t) = ⬕[n←w](＠v.t).
#n #w #v #t //
qed.
