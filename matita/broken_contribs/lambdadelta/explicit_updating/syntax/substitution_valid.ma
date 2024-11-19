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

include "explicit_updating/syntax/term_valid.ma".
include "explicit_updating/syntax/substitution.ma".

(* VALIDITY FOR SUBSTITUTION ************************************************)

definition subst_valid (b): predicate (𝕊) ≝
           λS. ∀p. b ⊢ S＠⧣❨p❩.

interpretation
  "validity (substitution)"
  'VDash b S = (subst_valid b S).
