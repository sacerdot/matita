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
include "explicit_updating/syntax/term_flat_next.ma".

(* FLATTENING FOR TERM ******************************************************)

(* Constructions with term_lref *********************************************)

lemma term_flat_lref (p):
      𝛏❨p❩ = ♭𝛏❨p❩.
#p elim p -p //
qed.
