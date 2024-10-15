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
include "ground/notation/functions/compose_2.ma".
include "explicit_updating/syntax/substitution.ma".

(* COMPOSITION WITH RELOCATION FOR SUBSTITUTION *****************************)

definition subst_after (S:𝕊) (f:𝔽𝔹): 𝕊 ≝
           λp. S＠⧣❨f＠⧣❨p❩❩
.

interpretation
  "composition with relocation (substitution)"
  'Compose S f = (subst_after S f).

(* Basic constructions ******************************************************)

lemma subst_after_dapp (S) (f) (p):
      S＠⧣❨f＠⧣❨p❩❩ = (S•f)＠⧣❨p❩.
//
qed.
