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

include "ground/arith/ynat_plus.ma".
include "ground/arith/ynat_lminus.ma".
include "ground/arith/ynat_lt_pred_succ.ma".

(* STRICT ORDER FOR NON-NEGATIVE INTEGERS WITH INFINITY *********************)

(* Constructions with ylminus and yplus *************************************)

(*** ylt_plus1_to_minus_inj2 *)
lemma ylt_plus_sx_dx_lminus_dx (n) (x) (z):
      x + yinj_nat n < z → x < z - n.
#n @(nat_ind_succ … n) -n //
#n #IH #x #z >ysucc_inj <yplus_succ_shift
/3 width=1 by ylt_des_succ_sx/
qed.

(*** ylt_plus1_to_minus_inj1 *)
lemma ylt_plus_sx_sx_lminus_dx (n) (x) (z):
      yinj_nat n + x < z → x < z - n.
/2 width=1 by ylt_plus_sx_dx_lminus_dx/ qed.
