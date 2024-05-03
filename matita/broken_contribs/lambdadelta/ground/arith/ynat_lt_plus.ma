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

include "ground/arith/nat_lt_plus.ma".
include "ground/arith/ynat_plus.ma".
include "ground/arith/ynat_lt_succ.ma".

(* STRICT ORDER FOR NON-NEGATIVE INTEGERS WITH INFINITY *********************)

(* Constructions with yplus *************************************************)

(*** ylt_plus_Y *)
lemma ylt_plus_inf (x) (y):
      x < ∞ → y < ∞ → x + y < ∞.
#x #y #Hx #Hy
elim (ylt_des_gen_sn … Hx) -Hx #m #H destruct
elim (ylt_des_gen_sn … Hy) -Hy #n #H destruct
//
qed.

(*** ylt_plus_dx1_trans *)
lemma ylt_plus_dx_sn (z) (x) (y):
      z < x → z < x + y.
#z #x #y * -z -x //
#o #m #Hom @(ynat_split_nat_inf … y) - y //
/3 width=1 by ylt_inj, nlt_plus_dx_dx/
qed.

(*** ylt_plus_dx2_trans *)
lemma ylt_plus_dx_dx (z) (x) (y):
      z < y → z < x + y.
#z #x #y <yplus_comm
/2 width=1 by ylt_plus_dx_sn/
qed.

(*** monotonic_ylt_plus_dx_inj *)
lemma ylt_plus_bi_dx_inj (o) (x) (y):
      x < y → x + yinj_nat o < y + yinj_nat o.
#o #x #y #Hxy
@(nat_ind_succ … o) -o //
#n #IH >ysucc_inj <yplus_succ_dx <yplus_succ_dx
/2 width=1 by ylt_succ_bi/
qed.

(*** monotonic_ylt_plus_sn_inj *)
lemma ylt_plus_bi_sn_inj (o) (x) (y):
      x < y → yinj_nat o + x < yinj_nat o + y.
/2 width=1 by ylt_plus_bi_dx_inj/ qed.

(*** monotonic_ylt_plus_dx *)
lemma ylt_plus_bi_dx (z) (x) (y):
      x < y → z < ∞ → x + z < y + z.
#z #x #y #Hxy #Hz
elim (ylt_des_gen_sn … Hz) -Hz #o #H destruct
/2 width=1 by ylt_plus_bi_dx_inj/
qed.

(*** monotonic_ylt_plus_sn *)
lemma ylt_plus_bi_sn (z) (x) (y):
      x < y → z < ∞ → z + x < z + y.
#z #x #y #Hxy #Hz <yplus_comm <yplus_comm in ⊢ (??%);
/2 width=1 by ylt_plus_bi_dx/
qed.

(* Inversions with yplus ****************************************************)

(*** yplus_inv_monotonic_dx *)
lemma eq_inv_yplus_bi_dx (z) (x) (y):
      z < ∞ → x + z = y + z → x = y.
#z #x #y #H
elim (ylt_des_gen_sn … H) -H #o #H destruct
/2 width=2 by eq_inv_yplus_bi_dx_inj/
qed-.

(*** yplus_inv_monotonic_23 *)
lemma yplus_inv_plus_bi_23 (z) (x1) (x2) (y1) (y2):
      z < ∞ → x1 + z + y1 = x2 + z + y2 → x1 + y1 = x2 + y2.
#z #x1 #x2 #y1 #y2 #Hz
<yplus_plus_comm_23 <yplus_plus_comm_23 in ⊢ (???%→?); #H
@(eq_inv_yplus_bi_dx … H) // (* * auto does not work *)
qed-.

(*** ylt_inv_plus_Y *)
lemma ylt_inv_plus_inf (x) (y):
      x + y < ∞ → ∧∧ x < ∞ & y < ∞.
#x #y #H
elim (ylt_des_gen_sn … H) -H #o #H
elim (eq_inv_yplus_inj … H) -H
/2 width=1 by conj/
qed-.

(* Destructions with yplus **************************************************)

(*** ylt_inv_monotonic_plus_dx *)
lemma ylt_des_plus_bi_dx (z) (x) (y):
      x + z < y + z → x < y.
#z @(ynat_split_nat_inf … z) -z
[ #o #x @(ynat_split_nat_inf … x) -x
  [ #m #y @(ynat_split_nat_inf … y) -y //
    #n <yplus_inj_bi <yplus_inj_bi #H
    /4 width=2 by ylt_inv_inj_bi, ylt_inj, nlt_inv_plus_bi_dx/
  | #y <yplus_inf_sn #H
    elim (ylt_inv_inf_sn … H)
  ]
| #x #y <yplus_inf_dx #H
  elim (ylt_inv_inf_sn … H)
]
qed-.

lemma ylt_des_plus_bi_sn (z) (x) (y):
      z + x < z + y → x < y.
/2 width=2 by ylt_des_plus_bi_dx/ qed-.
