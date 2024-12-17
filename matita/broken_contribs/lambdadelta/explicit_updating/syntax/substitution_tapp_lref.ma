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
include "explicit_updating/syntax/substitution_tapp.ma".

(* TERM APPLICATION FOR SUBSTITUTION ****************************************)

(* Constructions with term_lref *********************************************)

lemma subst_tapp_lref (p) (S):
      S＠⧣❨p❩ = S＠⧣❨𝛏❨p❩❩.
#p elim p -p //
#p #IH #S
<term_lref_succ <subst_tapp_lift <IH -IH //
qed.
