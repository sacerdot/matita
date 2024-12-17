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

include "explicit_updating/syntax/substitution_flat_tapp.ma".
include "explicit_updating/syntax/substitution_flat_unwind.ma".
include "explicit_updating/syntax/unwind.ma".

(* UNWIND FOR TERM **********************************************************)

(* Constructions with term_flat *********************************************)

lemma unwind_flat (f) (t):
      ▼[f]♭t ≐ ♭▼[f]t.
/4 width=3 by subst_flat_tapp, subst_tapp_eq_repl, term_eq_trans/
qed.
