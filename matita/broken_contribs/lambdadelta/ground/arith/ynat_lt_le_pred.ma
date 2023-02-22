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

include "ground/arith/ynat_le.ma".
include "ground/arith/ynat_lt_pred.ma".

(* STRICT ORDER FOR NON-NEGATIVE INTEGERS WITH INFINITY *********************)

(* Destructions with yle and ypred ******************************************)

(*** ylt_fwd_le_pred2 *)
lemma ylt_des_le_pred_dx (x) (y): x < y → x ≤ ↓y.
#x #y * -x -y //
#m #n #H
elim (nlt_inv_gen … H) -H #Hm #_
/2 width=1 by yle_inj/
qed-.
