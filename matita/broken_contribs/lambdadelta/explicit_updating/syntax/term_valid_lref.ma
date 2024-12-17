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

include "explicit_updating/syntax/term_lref.ma".
include "explicit_updating/syntax/term_valid_next.ma".

(* VALIDITY FOR TERM ********************************************************)

(* Constructions with term_lref *********************************************)

lemma term_valid_lref (b) (p):
      b ⊢ 𝛏p.
#b #p elim p -p
/2 width=1 by term_valid_next/
qed.
