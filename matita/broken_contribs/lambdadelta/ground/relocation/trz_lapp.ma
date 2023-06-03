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

include "ground/relocation/trz_map.ma".
include "ground/arith/int_pred_succ.ma".
include "ground/notation/functions/atsection_2.ma".

(* LEVEL APPLICATION FOR TOTAL RELOCATION MAPS WITH INTEGERS ****************)

interpretation
  "level application (total relocation maps with integers)"
  'AtSection f z = (zpred (trz_staff f (zsucc z))).

(* Basic constructions ******************************************************)

lemma trz_dapp_succ_lapp (f) (z):
      ↑f＠§❨z❩ = f＠⧣❨↑z❩.
// qed.

lemma trz_dapp_lapp (f) (z):
      ↑f＠§❨↓z❩ = f＠⧣❨z❩.
// qed.

lemma trz_lapp_pred_dapp (f) (z):
      ↓f＠⧣❨z❩ = f＠§❨↓z❩.
// qed.

lemma trz_eq_ext_lapp (f1) (f2):
      (∀z. f1＠§❨z❩ = f2＠§❨z❩) → f1 ≐ f2.
#f1 #f2 #Hf #z0
<trz_dapp_lapp <trz_dapp_lapp in ⊢ (???%); //
qed-.

lemma trz_lapp_eq_repl (z):
      compatible_2_fwd … trz_eq (eq …) (λf.f＠§❨z❩).
/2 width=1 by trz_dapp_eq_repl/
qed.
