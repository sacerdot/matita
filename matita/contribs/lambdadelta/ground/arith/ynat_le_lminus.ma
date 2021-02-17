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

include "ground/arith/nat_le_minus.ma".
include "ground/arith/ynat_lminus.ma".
include "ground/arith/ynat_le.ma".

(* ORDER FOR NON-NEGATIVE INTEGERS WITH INFINITY ****************************)

(* Constructions with ylminus ***********************************************)

(*** yle_minus_sn *)
lemma yle_lminus_sn_refl_sn (x) (n): x - n ≤ x.
#x @(ynat_split_nat_inf … x) -x //
#m #n /2 width=1 by yle_inj/
qed.

(*** monotonic_yle_minus_dx *)
lemma yle_lminus_bi_dx (o) (x) (y):
      x ≤ y → x - o ≤ y - o.
#o #x #y *
/3 width=1 by nle_minus_bi_dx, yle_inj, yle_inf/
qed.

(*** yminus_to_le *)
lemma yle_eq_zero_lminus (x) (n): 𝟎 = x - n → x ≤ yinj_nat n.
#x @(ynat_split_nat_inf … x) -x
[ #m #n <ylminus_inj_sn >yinj_nat_zero #H
  /4 width=1 by nle_eq_zero_minus, yle_inj, eq_inv_yinj_nat_bi/
| #n <ylminus_inf_sn #H destruct
]
qed.

(* Inversions with ylminus **************************************************)

(*** yle_to_minus *)
lemma yle_inv_eq_zero_lminus (x) (n):
      x ≤ yinj_nat n → 𝟎 = x - n.
#x @(ynat_split_nat_inf … x) -x
[ #m #n #H <ylminus_inj_sn
  <nle_inv_eq_zero_minus /2 width=1 by yle_inv_inj_bi/
| #n #H
  lapply (yle_inv_inf_sn … H) -H #H
  elim (eq_inv_inf_yinj_nat … H)
]
qed-.
