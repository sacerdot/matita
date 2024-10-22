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

include "explicit_updating/syntax/substitution_unwind_eq.ma".
include "explicit_updating/syntax/substitution_tapp_eq.ma".
include "explicit_updating/syntax/unwind.ma".

(* UNWIND FOR TERM *********************************************************)

(* Constructions with term_eq **********************************************)

lemma unwind_eq_repl:
      compatible_3 … fbr_eq term_eq term_eq unwind.
#f1 #f2 #Hf
/3 width=1 by subst_tapp_eq_repl, subst_unwind_eq_repl/
qed.

lemma unwind_lift (f) (g) (t):
      ▼[f•g]t ≐ ▼[f](𝛗g.t).
#f #g #t
<unwind_unfold <unwind_unfold <subst_tapp_lift
/2 width=1 by subst_tapp_eq_repl/
qed.
