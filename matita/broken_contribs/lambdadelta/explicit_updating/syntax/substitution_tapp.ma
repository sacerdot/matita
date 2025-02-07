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

include "explicit_updating/syntax/substitution_after.ma".
include "explicit_updating/syntax/substitution_push.ma".

(* TERM APPLICATION FOR SUBSTITUTION ****************************************)

(* Source: AUT 55 (de Bruijn, 1978) *)
rec definition subst_tapp (S:𝕊) (t:𝕋) on t : 𝕋 ≝
match t with
[ unit     ⇒ S＠⧣❨𝟏❩
| abst b t ⇒ 𝛌b.(subst_tapp (⫯S) t)
| appl v t ⇒ ＠(subst_tapp S v).(subst_tapp S t)
| lift f t ⇒ subst_tapp (S•f) t
].

interpretation
  "term application (substitution)"
  'AtSharp S t = (subst_tapp S t).

(* Basic constructions ******************************************************)

lemma subst_tapp_unit (S):
      S＠⧣❨𝟏❩ = S＠⧣❨𝛏❩.
//
qed.

lemma subst_tapp_abst (S) (b) (t):
      (𝛌b.(⫯S＠⧣❨t❩)) = S＠⧣❨𝛌b.t❩.
//
qed.

lemma subst_tapp_appl (S) (v) (t):
      (＠(S＠⧣❨v❩).(S＠⧣❨t❩)) = S＠⧣❨＠v.t❩.
//
qed.

lemma subst_tapp_lift (S) (f) (t):
      (S•f)＠⧣❨t❩ = S＠⧣❨𝛗f.t❩.
//
qed.
