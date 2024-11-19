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

include "explicit_updating/syntax/term_valid_eq.ma".
include "explicit_updating/syntax/substitution_eq.ma".
include "explicit_updating/syntax/substitution_valid.ma".

(* VALIDITY FOR SUBSTITUTION ************************************************)

(* Constructions with term_eq ***********************************************)

lemma subst_valid_eq_repl_fwd (b):
      replace_1_fwd … subst_eq (subst_valid b).
/2 width=3 by term_valid_eq_repl_fwd/
qed-.

lemma subst_valid_eq_repl_bck (b):
      replace_1_back … subst_eq (subst_valid b).
/3 width=3 by subst_valid_eq_repl_fwd, subst_eq_sym/
qed-.
