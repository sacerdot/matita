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
include "explicit_updating/syntax/term_valid.ma".

(* VALIDITY FOR TERM ********************************************************)

(* Constructions with term_next *********************************************)

lemma term_valid_next (b) (t):
      b ⊢ t → b ⊢ ↑t.
/2 width=1 by term_valid_lift/
qed.

(* Inversions with term_next ************************************************)

lemma term_valid_inv_next (b) (t):
      b ⊢ ↑t → b ⊢ t.
/2 width=2 by term_valid_inv_lift/
qed-.
