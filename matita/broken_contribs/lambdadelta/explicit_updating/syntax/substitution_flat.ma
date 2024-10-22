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

include "explicit_updating/syntax/substitution.ma".
include "explicit_updating/syntax/term_flat.ma".

(* FLATTENING FOR SUBSTITUTION **********************************************)

definition subst_flat (S): 𝕊 ≝
           λp. ♭(S＠⧣❨p❩)
.

interpretation
  "flattening (substitution)"
  'Flat S = (subst_flat S).

(* Basic constructions ******************************************************)

lemma subst_flat_dapp (S) (p):
      ♭(S＠⧣❨p❩) = (♭S)＠⧣❨p❩.
//
qed.
