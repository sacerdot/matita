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

include "ground/arith/ynat_succ.ma".
include "ground/arith/ynat_lt_pred.ma".

(* STRICT ORDER FOR NON-NEGATIVE INTEGERS WITH INFINITY *********************)

(* Constructions with ypred and ysucc ***************************************)

(*** ylt_O1 *)
lemma ylt_zero_sx (y): y = ⫯⫰y → 𝟎 < y.
#y @(ynat_split_nat_inf … y) -y
/4 width=1 by ylt_inj, eq_inv_yinj_nat_bi, nlt_zero_sx/
qed.

(* Destructions with ypred and ysucc ****************************************)

(*** ylt_inv_O1 *)
lemma ylt_des_gen_dx (x) (y): x < y → y = ⫯⫰y.
#x #y * //
#m #n #H
lapply (nlt_des_gen … H) -H //
qed-.

lemma ylt_des_succ_sx (x) (y):
      (⫯x) < y → x < ⫰y.
#x #y @(insert_eq_1 … (⫯x))
#x0 * -x0 -y
[ #m0 #n #Hn #H
  elim (eq_inv_ysucc_inj … H) -H #m #H1 #H2 destruct
  elim (nlt_inv_succ_sx … Hn) -Hn #Hm #_
  /2 width=1 by ylt_inj/
| #m0 #H
  elim (eq_inv_ysucc_inj … H) -H #m #H1 #H2 destruct //
]
qed-.

(* Inversions with ypred and ysucc ******************************************)

(*** ylt_inv_succ1 *)
lemma ylt_inv_succ_sx (x) (y):
      (⫯x) < y → ∧∧ x < ⫰y & y = ⫯⫰y.
/3 width=2 by ylt_des_succ_sx, ylt_des_gen_dx, conj/ qed-.
