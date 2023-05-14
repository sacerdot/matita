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

include "ground/arith/ynat_pred_succ.ma".
include "ground/arith/ynat_plus.ma".
include "ground/arith/ynat_lt_pred_succ.ma".

(* STRICT ORDER FOR NON-NEGATIVE INTEGERS WITH INFINITY *********************)

(* Inversions with yplus and ypred ******************************************)

(*** yplus_inv_succ_lt_dx *)
lemma eq_inv_succ_yplus_lt_dx (z) (x) (y):  𝟎 < y → ⫯z = x + y → z = x + ⫰y.
#z #x #y #Hy >(ylt_des_gen_dx … Hy) -Hy
<yplus_succ_dx <ypred_succ
/2 width=1 by eq_inv_ysucc_bi/
qed-.

(*** yplus_inv_succ_lt_sn *)
lemma eq_inv_succ_yplus_lt_sn (z) (x) (y): 𝟎 < x → ⫯z = x + y → z = ⫰x + y.
/2 width=1 by eq_inv_succ_yplus_lt_dx/ qed-.

(* Destructions with yplus and ypred ****************************************)

(*** yplus_pred1 *)
lemma yplus_pred_sn (x) (y): 𝟎 < x → ⫰(x+y) = ⫰x + y.
#x #y #Hx >(ylt_des_gen_dx … Hx) -Hx
<yplus_succ_sn <ypred_succ <ypred_succ //
qed-.

(*** yplus_pred2 *)
lemma yplus_pred_dx (x) (y): 𝟎 < y → x + ⫰y = ⫰(x+y).
/2 width=1 by yplus_pred_sn/ qed-.

