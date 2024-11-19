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

include "explicit_updating/syntax/substitution_push.ma".
include "explicit_updating/syntax/substitution_valid.ma".

(* VALIDITY FOR SUBSTITUTION ************************************************)

(* Constructions with subst_push ********************************************)

lemma subst_valid_push (b) (S):
      b ⊢ S → b ⊢ ⫯S.
#b #S #HS *
/2 width=1 by term_valid_lift/
qed.

(* Inversions with subst_push ***********************************************)

lemma subst_valid_inv_push (b) (S):
      b ⊢ ⫯S → b ⊢ S.
#b #S #HS *
/2 width=2 by term_valid_inv_lift/
qed-.
