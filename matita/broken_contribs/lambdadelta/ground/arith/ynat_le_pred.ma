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

include "ground/arith/nat_le_pred.ma".
include "ground/arith/ynat_pred.ma".
include "ground/arith/ynat_le.ma".

(* ORDER FOR NON-NEGATIVE INTEGERS WITH INFINITY ****************************)

(* Constructions with ypred *************************************************)

(*** yle_pred_sn *)
lemma yle_pred_sn_trans (x) (y): x ≤ y → ↓x ≤ y.
#x #y * -x -y
/3 width=3 by yle_inj, nle_trans/
qed.

(*** yle_refl_pred_sn *)
lemma yle_pred_sn_refl (x): ↓x ≤ x.
/2 width=1 by yle_pred_sn_trans, yle_refl/ qed.

(*** yle_pred *)
lemma yle_pred_bi (x) (y): x ≤ y → ↓x ≤ ↓y.
#x #y * -x -y
/3 width=1 by yle_inj, nle_pred_bi/
qed.
