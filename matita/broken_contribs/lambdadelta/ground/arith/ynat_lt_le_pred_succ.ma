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

include "ground/arith/ynat_le_pred_succ.ma".
include "ground/arith/ynat_lt_pred_succ.ma".

(* STRICT ORDER FOR NON-NEGATIVE INTEGERS WITH INFINITY *********************)

(* Constructions with yle and ypred and ysucc *******************************)

(*** yle_inv_succ_sx_lt yle_inv_succ1_lt *)
lemma le_succ_sx_ylt (x) (y):
      (⫯x) ≤ y → ∧∧ x ≤ ⫰y & 𝟎 < y.
#x #y #H elim (yle_inv_succ_sx … H) -H
/4 width=2 by ylt_zero_sx, conj/
qed-.
