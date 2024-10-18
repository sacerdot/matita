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

include "explicit_updating/syntax/substitution_pushs_eq.ma".
include "explicit_updating/syntax/substitution_beta_eq.ma".
include "explicit_updating/syntax/substitution_tapp_eq.ma".
include "explicit_updating/syntax/beta.ma".

(* β-SUBSTITUTION FOR TERM **************************************************)

(* Constructions with α-equivalence for term ********************************)

lemma beta_eq_repl:
      compatible_4 … (eq …) term_eq term_eq term_eq beta.
/4 width=1 by subst_tapp_eq_repl, subst_pushs_eq_repl, subst_beta_eq_repl/
qed.
