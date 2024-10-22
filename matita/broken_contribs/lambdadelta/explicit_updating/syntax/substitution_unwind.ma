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

include "ground/relocation/fb/fbr_dapp.ma".
include "explicit_updating/syntax/substitution.ma".
include "explicit_updating/notation/functions/element_s_1.ma".

(* SUBSTITUTION FOR UNWIND **************************************************)

definition subst_unwind (f): 𝕊 ≝ λp.𝛏(f＠⧣❨p❩).

interpretation
  "for unwind (substitution)"
  'ElementS f = (subst_unwind f).

(* Basic constructions ******************************************************)

lemma subst_unwind_dapp (f) (p):
      (𝛏(f＠⧣❨p❩)) = 𝐬❨f❩＠⧣❨p❩.
// qed.
