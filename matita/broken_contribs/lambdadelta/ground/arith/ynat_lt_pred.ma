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

include "ground/arith/nat_lt_pred.ma".
include "ground/arith/ynat_pred.ma".
include "ground/arith/ynat_lt.ma".

(* STRICT ORDER FOR NON-NEGATIVE INTEGERS WITH INFINITY *********************)

(* Constructions with ypred *************************************************)

(*** ylt_pred *)
lemma ylt_pred_bi (x) (y):
      x < y → 𝟎 < x → ⫰x < ⫰y.
#x #y * -x -y
/4 width=1 by ylt_inv_inj_bi, ylt_inj, nlt_pred_bi/
qed.
