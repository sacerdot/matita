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

include "ground/arith/pnat_split.ma".
include "explicit_updating/syntax/substitution.ma".
include "explicit_updating/notation/functions/element_s_1.ma".

(* SUBSTITUTION FOR β-REDUCTION *********************************************)

definition subst_beta (v): 𝕊 ≝
           psplit … v (λp.ξp).

interpretation
  "for β-reduction (substitution)"
  'ElementS v = (subst_beta v).

(* Basic constructions ******************************************************)

lemma subst_beta_dapp_unit (v):
      v = 𝐬❨v❩＠⧣❨𝟏❩.
// qed.

lemma subst_beta_dapp_succ (v) (p):
      ξp = 𝐬❨v❩＠⧣❨↑p❩.
// qed.
