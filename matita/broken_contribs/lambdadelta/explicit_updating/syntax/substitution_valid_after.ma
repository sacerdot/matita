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

include "explicit_updating/syntax/substitution_after.ma".
include "explicit_updating/syntax/substitution_valid.ma".

(* VALIDITY FOR SUBSTITUTION *************************************************)

(* Constructions with subst_after ********************************************)

lemma subst_valid_after (b) (S) (f):
      b ⊢ S → b ⊢ S•f.
//
qed.
