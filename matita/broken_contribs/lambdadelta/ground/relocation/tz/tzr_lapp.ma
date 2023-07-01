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

include "ground/relocation/tz/tzr_map.ma".
include "ground/arith/int_pred_succ.ma".
include "ground/notation/functions/atsection_2.ma".

(* LEVEL APPLICATION FOR TOTAL RELOCATION MAPS WITH INTEGERS ****************)

interpretation
  "level application (total relocation maps with integers)"
  'AtSection f z = (zpred (tzr_staff f (zsucc z))).

(* Basic constructions ******************************************************)

lemma tzr_dapp_succ_lapp (f) (z):
      ↑f＠§❨z❩ = f＠⧣❨↑z❩.
// qed.

lemma tzr_dapp_lapp (f) (z):
      ↑f＠§❨↓z❩ = f＠⧣❨z❩.
// qed.

lemma tzr_lapp_pred_dapp (f) (z):
      ↓f＠⧣❨z❩ = f＠§❨↓z❩.
// qed.

lemma tzr_eq_ext_lapp (f1) (f2):
      (∀z. f1＠§❨z❩ = f2＠§❨z❩) → f1 ≐ f2.
#f1 #f2 #Hf #z0
<tzr_dapp_lapp <tzr_dapp_lapp in ⊢ (???%); //
qed-.

lemma tzr_lapp_eq_repl (z):
      compatible_2_fwd … tzr_eq (eq …) (λf.f＠§❨z❩).
/2 width=1 by tzr_dapp_eq_repl/
qed.
