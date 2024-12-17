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

include "explicit_updating/syntax/substitution_tapp_lref.ma".
include "explicit_updating/syntax/beta.ma".

(* β-SUBSTITUTION FOR TERM **************************************************)

(* Constructions with term_lref *********************************************)

lemma beta_zero_lref_succ (v) (p):
      (𝛏❨p❩) = ⬕[𝟎←v]𝛏❨↑p❩.
#v #p
<beta_unfold //
qed.
