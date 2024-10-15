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

include "explicit_updating/syntax/term_next_eq.ma".
include "explicit_updating/syntax/substitution_eq.ma".
include "explicit_updating/syntax/substitution_push.ma".

(* PUSH FOR SUBSTITUTION ****************************************************)

(* Constructions with extensional equivalence for substitution **************)

lemma subst_push_eq_repl:
      compatible_2_fwd … subst_eq subst_eq subst_push.
#S1 #S2 #HS * //
/3 width=1 by subst_dapp_eq_repl, term_next_eq_repl/
qed.
