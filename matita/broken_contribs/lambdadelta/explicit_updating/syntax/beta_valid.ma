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

include "explicit_updating/syntax/substitution_valid_pushs.ma".
include "explicit_updating/syntax/substitution_valid_tapp.ma".
include "explicit_updating/syntax/substitution_valid_beta.ma".
include "explicit_updating/syntax/beta.ma".

(* β-SUBSTITUTION FOR TERM **************************************************)

(* Constructions with valid_term ********************************************)

lemma beta_valid (b) (n) (v) (t):
      b ⊢ v → b ⊢ t → b ⊢ ⬕[n←v]t.
/4 width=1 by substitution_valid_beta, subst_valid_tapp, subst_valid_pushs/
qed.
