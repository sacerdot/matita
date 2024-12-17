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

include "explicit_updating/syntax/term_flat.ma".
include "explicit_updating/syntax/term_valid.ma".

(* VALIDITY FOR TERM ********************************************************)

(* Constructions with term_flat *********************************************)

lemma term_valid_flat (b) (t):
      b ⊢ ♭t.
#b #t elim t -t
/2 width=1 by term_valid_unit, term_valid_abst, term_valid_appl, term_valid_lift/
qed.

(* Inversions with term_flat ************************************************)

lemma term_valid_inv_false_eq_flat_refl (t):
      (ⓕ) ⊢ t → ♭t = t.
#t #Ht elim Ht -t
/2 width=1 by eq_f2/
qed-.
