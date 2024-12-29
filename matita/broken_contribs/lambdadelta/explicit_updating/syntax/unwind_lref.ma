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
include "explicit_updating/syntax/unwind.ma".

(* UNWIND FOR TERM **********************************************************)

(* Constructions with term_lref *********************************************)

lemma unwind_lref (f) (p):
      (𝛏❨f＠⧣❨p❩❩) = ▼[f]𝛏❨p❩.
//
qed.

lemma unwind_id_lref (p):
      (𝛏❨p❩) = ▼[𝐢]𝛏❨p❩.
#p <unwind_lref //
qed.

lemma unwind_unit_lref (f):
      (𝛏❨f＠⧣❨𝟏❩❩) = ▼[f]𝛏.
//
qed.
