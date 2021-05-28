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

include "ground/xoa/ex_3_2.ma".
include "ground/arith/nat_plus.ma".
include "ground/arith/ynat_succ.ma".

(* ADDITION FOR NON-NEGATIVE INTEGERS WITH INFINITY *************************)

definition yplus_aux (x) (n): ynat ≝
           (ysucc^n) x.

(*** yplus *)
definition yplus (x): ynat → ynat ≝
           ynat_bind_nat (yplus_aux x) (∞).

interpretation
  "plus (non-negative integers with infinity)"
  'plus x y = (yplus x y).

(* Basic constructions ******************************************************)

lemma yplus_inj_dx (x) (n):
      (ysucc^n) x = x + yinj_nat n.
#x @(ynat_bind_nat_inj (yplus_aux x))
qed.

(*** yplus_Y2 *)
lemma yplus_inf_dx (x): ∞ = x + ∞.
// qed.

(*** yplus_O2 *)
lemma yplus_zero_dx (x): x = x + 𝟎.
// qed.

(* Constructions with ysucc *************************************************)

(*** yplus_SO2 *)
lemma yplus_one_dx (x): ↑x = x + 𝟏.
// qed.

(*** yplus_S2 yplus_succ2 *)
lemma yplus_succ_dx (x1) (x2): ↑(x1 + x2) = x1 + ↑x2.
#x1 #x2 @(ynat_split_nat_inf … x2) -x2 //
#n2 <ysucc_inj <yplus_inj_dx <yplus_inj_dx
@niter_succ
qed.

(*** yplus_succ1 *)
lemma yplus_succ_sn (x1) (x2): ↑(x1 + x2) = ↑x1 + x2.
#x1 #x2 @(ynat_split_nat_inf … x2) -x2 //
#n2 <yplus_inj_dx <yplus_inj_dx
@niter_appl
qed.

(*** yplus_succ_swap *)
lemma yplus_succ_shift (x1) (x2): ↑x1 + x2 = x1 + ↑x2.
// qed-.

(* Constructions with nplus *************************************************)

(*** yplus_inj *)
lemma yplus_inj_bi (n) (m):
      yinj_nat (m + n) = yinj_nat m + yinj_nat n.
#n @(nat_ind_succ … n) -n //
#n #IH #m
<nplus_succ_dx >ysucc_inj >ysucc_inj <yplus_succ_dx //
qed.

(* Advanced constructions ***************************************************)

(*** ysucc_iter_Y yplus_Y1 *)
lemma yplus_inf_sn (x): ∞ = ∞ + x.
#x @(ynat_ind_succ … x) -x //
#n #IH <yplus_succ_dx //
qed.

(*** yplus_O1 *)
lemma yplus_zero_sn (x): x = 𝟎 + x.
#x @(ynat_split_nat_inf … x) -x //
qed.

(*** yplus_comm *)
lemma yplus_comm: commutative … yplus.
#x1 @(ynat_split_nat_inf … x1) -x1 //
#n1 #x2 @(ynat_split_nat_inf … x2) -x2 //
#n2 <yplus_inj_bi <yplus_inj_bi //
qed.

(*** yplus_assoc *)
lemma yplus_assoc: associative … yplus.
#x1 #x2 @(ynat_split_nat_inf … x2) -x2 //
#n2 #x3 @(ynat_split_nat_inf … x3) -x3 //
#n3 @(ynat_split_nat_inf … x1) -x1 //
<yplus_inf_sn //
qed.

(*** yplus_comm_23 *)
lemma yplus_plus_comm_23 (z) (x) (y):
      z + x + y = z + y + x.
#z #x #y >yplus_assoc //
qed.

lemma yplus_plus_comm_13 (x) (y) (z):
      x + z + y = y + z + x.
// qed.

(*** yplus_comm_24 *)
lemma yplus_plus_comm_24 (x1) (x4) (x2) (x3):
      x1 + x4 + x3 + x2 = x1 + x2 + x3 + x4.
#x1 #x4 #x2 #x3
>yplus_assoc >yplus_assoc >yplus_assoc >yplus_assoc //
qed.

(*** yplus_assoc_23 *)
lemma yplus_plus_assoc_23 (x1) (x4) (x2) (x3):
      x1 + (x2 + x3) + x4 = x1 + x2 + (x3 + x4).
#x1 #x4 #x2 #x3
>yplus_assoc >yplus_assoc //
qed.

(* Basic inversions *********************************************************)

(*** yplus_inv_Y1 *)
lemma eq_inv_inf_plus (x) (y):
      ∞ = x + y → ∨∨ ∞ = x | ∞ = y.
#x @(ynat_split_nat_inf … x) -x /2 width=1 by or_introl/
#m #y @(ynat_split_nat_inf … y) -y /2 width=1 by or_introl/
#n <yplus_inj_bi #H
elim (eq_inv_inf_yinj_nat … H)
qed-.

(*** yplus_inv_Y2 *)
lemma eq_inv_plus_inf (x) (y):
      x + y = ∞ → ∨∨ ∞ = x | ∞ = y.
/2 width=1 by eq_inv_inf_plus/ qed-.

(*** discr_yplus_x_xy discr_yplus_xy_x *)
lemma yplus_refl_sn (x) (y):
      x = x + y → ∨∨ ∞ = x | 𝟎 = y.
#x @(ynat_split_nat_inf … x) -x /2 width=1 by or_introl/
#m #y @(ynat_split_nat_inf … y) -y /2 width=1 by or_introl/
#n <yplus_inj_bi #H
lapply (eq_inv_yinj_nat_bi … H) -H #H
<(nplus_refl_sn … H) -n //
qed-.

(*** yplus_inv_monotonic_dx_inj *)
lemma eq_inv_yplus_bi_dx_inj (o) (x) (y):
      x + yinj_nat o = y + yinj_nat o → x = y.
#o @(nat_ind_succ … o) -o //
#o #IH #x #y >ysucc_inj <yplus_succ_dx <yplus_succ_dx #H
/3 width=1 by eq_inv_ysucc_bi/
qed-.

lemma eq_inv_yplus_bi_sn_inj (o) (x) (y):
      yinj_nat o + x = yinj_nat o + y → x = y.
/2 width=2 by eq_inv_yplus_bi_dx_inj/ qed-.

(* Inversions with nplus ****************************************************)

(*** yplus_inv_inj *)
lemma eq_inv_inj_yplus (o) (x) (y):
      yinj_nat o = x + y →
      ∃∃m,n. o = m + n & x = yinj_nat m & y = yinj_nat n.
#o #x @(ynat_split_nat_inf … x) -x
[| #y <yplus_inf_sn #H elim (eq_inv_yinj_nat_inf … H) ]
#m #y @(ynat_split_nat_inf … y) -y
[| #H elim (eq_inv_yinj_nat_inf … H) ]
#n <yplus_inj_bi #H
/3 width=5 by eq_inv_yinj_nat_bi, ex3_2_intro/
qed-.

lemma eq_inv_yplus_inj (o) (x) (y):
      x + y = yinj_nat o →
      ∃∃m,n. o = m + n & x = yinj_nat m & y = yinj_nat n.
#o #x #y <yplus_comm
/2 width=1 by eq_inv_inj_yplus/
qed-.

(* Advanced inversions ******************************************************)

(*** yplus_inv_O *)
lemma eq_inv_zero_yplus (x) (y):
      (𝟎) = x + y → ∧∧ 𝟎 = x & 𝟎 = y.
#x #y #H
elim (eq_inv_inj_yplus (𝟎) ?? H) -H #m #n #H #H1 #H2 destruct
elim (eq_inv_zero_nplus … H) -H #H1 #H2 destruct
/2 width=1 by conj/
qed-.
