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

include "explicit_updating/syntax/substitution_valid_tapp.ma".
include "explicit_updating/syntax/substitution_valid_unwind.ma".
include "explicit_updating/syntax/unwind.ma".

(* UNWIND FOR TERM **********************************************************)

(* Constructions with valid_term ********************************************)

lemma unwind_valid (b) (f) (t):
      b ⊢ t → b ⊢ ▼[f]t.
/2 width=1 by substitution_valid_unwind, subst_valid_tapp/
qed.
