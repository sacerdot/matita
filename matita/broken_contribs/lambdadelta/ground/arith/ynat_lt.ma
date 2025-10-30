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

include "ground/arith/nat_lt.ma".
include "ground/arith/ynat_nat.ma".

(* STRICT ORDER FOR NON-NEGATIVE INTEGERS WITH INFINITY *********************)

(*** ylt *)
inductive ylt: relation ynat ≝
| ylt_inj: ∀m,n. m < n → ylt (yinj_nat m) (yinj_nat n)
| ylt_inf: ∀m. ylt (yinj_nat m) (∞)
.

interpretation
  "less (non-negative integers with infinity)"
  'lt x y = (ylt x y).

(* Basic destructions *******************************************************)

(*** ylt_fwd_gen ylt_inv_Y2 *)
lemma ylt_des_gen_sx (x) (y):
      x < y → ∃m. x = yinj_nat m.
#x #y * -x -y
/2 width=2 by ex_intro/
qed-.

lemma ylt_des_lt_inf_dx (x) (y): x < y → x < ∞.
#x #y #H
elim (ylt_des_gen_sx … H) -y #m #H destruct //
qed-.

(*** ylt_fwd_lt_O1 *)
lemma ylt_des_lt_zero_sx (x) (y): x < y → 𝟎 < y.
#x #y * -x -y
/3 width=2 by ylt_inf, ylt_inj, nlt_des_lt_zero_sx/
qed-.

(* Basic inversions *********************************************************)

(*** ylt_inv_inj2 *)
lemma ylt_inv_inj_dx (x) (n):
      x < yinj_nat n →
      ∃∃m. m < n & x = yinj_nat m.
#x #n0 @(insert_eq_1 … (yinj_nat n0))
#y * -x -y
[ #m #n #Hmn #H >(eq_inv_yinj_nat_bi … H) -n0
  /2 width=3 by ex2_intro/
| #m0 #H elim (eq_inv_yinj_nat_inf … H)
]
qed-.

(*** ylt_inv_inj *)
lemma ylt_inv_inj_bi (m) (n):
      yinj_nat m < yinj_nat n → m < n.
#m #n #H elim (ylt_inv_inj_dx … H) -H
#x #Hx #H >(eq_inv_yinj_nat_bi … H) -m //
qed-.

(*** ylt_inv_Y1 *)
lemma ylt_inv_inf_sx (y): ∞ < y → ⊥.
#y #H elim (ylt_des_gen_sx … H) -H
#n #H elim (eq_inv_inf_yinj_nat … H)
qed-.

lemma ylt_inv_refl (x): x < x → ⊥.
#x @(ynat_split_nat_inf … x) -x
/3 width=2 by ylt_inv_inf_sx, ylt_inv_inj_bi, nlt_inv_refl/
qed-.

(* Main constructions *******************************************************)

(*** ylt_trans *)
theorem ylt_trans: Transitive … ylt.
#x #y * -x -y
[ #m #n #Hxy #z @(ynat_split_nat_inf … z) -z
  /4 width=3 by ylt_inv_inj_bi, ylt_inj, nlt_trans/
| #m #z #H elim (ylt_inv_inf_sx … H)
]
qed-.

(*** lt_ylt_trans *)
lemma lt_ylt_trans (m) (n) (z):
      m < n → yinj_nat n < z → yinj_nat m < z.
/3 width=3 by ylt_trans, ylt_inj/
qed-.
