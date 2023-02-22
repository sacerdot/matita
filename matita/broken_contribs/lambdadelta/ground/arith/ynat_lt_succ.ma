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
include "ground/arith/ynat_lt.ma".

(* STRICT ORDER FOR NON-NEGATIVE INTEGERS WITH INFINITY *********************)

(* Constructions with ysucc *************************************************)

(*** ylt_O_succ *)
lemma ylt_zero_succ (y): 𝟎 < ↑y.
#y @(ynat_split_nat_inf … y) -y
/2 width=1 by ylt_inj/
qed.

(*** ylt_succ *)
lemma ylt_succ_bi (x) (y): x < y → ↑x < ↑y.
#x #y * -x -y
/3 width=1 by ylt_inj, ylt_inf, nlt_succ_bi/
qed.

(*** ylt_succ_Y *)
lemma ylt_succ_inf (x): x < ∞ → ↑x < ∞.
#x @(ynat_split_nat_inf … x) -x //
qed.

(*** ylt_succ2_refl *)
lemma ylt_succ_dx_refl (x) (y): x < y → x < ↑x.
#x #y #H
elim (ylt_des_gen_sn … H) -y #n #H destruct
/2 width=1 by ylt_inj/
qed.

(* Inversions with ysucc ****************************************************)

lemma ylt_inv_succ_inf (x): ↑x < ∞ → x < ∞.
#x #H
elim (ylt_des_gen_sn … H) -H #m0 #H
elim (eq_inv_ysucc_inj … H) -H #m #H1 #H2 destruct //
qed-.

(*** ylt_inv_succ *)
lemma ylt_inv_succ_bi (x) (y): ↑x < ↑y → x < y.
#x #y @(ynat_split_nat_inf … y) -y
[ #n <ysucc_inj #H
  elim (ylt_inv_inj_dx … H) -H #m0 #Hmn #H
  elim (eq_inv_ysucc_inj … H) -H #m #H1 #H2 destruct
  /3 width=1 by ylt_inj, nlt_inv_succ_bi/
| /2 width=1 by ylt_inv_succ_inf/
]
qed-.
