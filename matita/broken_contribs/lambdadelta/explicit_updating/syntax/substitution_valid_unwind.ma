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

include "explicit_updating/syntax/substitution_unwind.ma".
include "explicit_updating/syntax/substitution_valid.ma".

(* VALIDITY FOR SUBSTITUTION ************************************************)

(* Constructions with subst_unwind ******************************************)

lemma substitution_valid_unwind (b) (f):
      b ⊢ 𝐬❨f❩.
//
qed.
