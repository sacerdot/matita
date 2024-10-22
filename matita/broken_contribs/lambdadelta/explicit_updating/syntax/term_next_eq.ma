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

include "explicit_updating/syntax/term_eq.ma".
include "explicit_updating/syntax/term_next.ma".

(* NEXT FOR TERM ************************************************************)

(* Constructions with term_eq ***********************************************)

lemma term_next_eq_repl:
      compatible_2_fwd … term_eq term_eq term_next.
/2 width=1 by term_eq_lift/
qed.
