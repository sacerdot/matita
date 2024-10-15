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

include "explicit_updating/syntax/term_next.ma".
include "explicit_updating/syntax/substitution.ma".

(* PUSH FOR SUBSTITUTION ****************************************************)

definition subst_push (S): 𝕊 ≝
           psplit … (ξ𝟏) (λp.↑(S＠⧣❨p❩))
.

interpretation
  "push (substitution)"
  'UpSpoon S = (subst_push S).

(* Basic constructions ******************************************************)

lemma subst_push_unit (S):
      (ξ𝟏) = (⫯S)＠⧣❨𝟏❩.
// qed.

lemma subst_push_succ (S) (p):
      ↑(S＠⧣❨p❩) = (⫯S)＠⧣❨↑p❩.
// qed.
