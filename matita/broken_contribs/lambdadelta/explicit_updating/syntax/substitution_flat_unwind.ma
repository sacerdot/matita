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

include "explicit_updating/syntax/term_flat_lref.ma".
include "explicit_updating/syntax/substitution_eq.ma".
include "explicit_updating/syntax/substitution_unwind.ma".
include "explicit_updating/syntax/substitution_flat.ma".

(* FLATTENING FOR SUBSTITUTION **********************************************)

(* Constructions with subst_unwind ******************************************)

lemma subst_flat_unwind (f):
      (𝐬❨f❩) ≐ ♭𝐬❨f❩.
//
qed.
