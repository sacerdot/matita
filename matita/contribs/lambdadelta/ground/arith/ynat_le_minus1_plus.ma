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

include "ground/arith/nat_le_minus_plus.ma".
include "ground/arith/ynat_minus1_plus.ma".
include "ground/arith/ynat_le_plus.ma".
include "ground/arith/ynat_le_minus1.ma".

(* ORDER FOR NON-NEGATIVE INTEGERS WITH INFINITY ****************************)

(* Constructions with yminus and yplus **************************************)

(*** yle_plus1_to_minus_inj2 *)
lemma yle_plus_sn_dx_minus1_dx (n) (x) (z):
      x + yinj_nat n ≤ z → x ≤ z - n.
#n #x #z #H
lapply (yle_minus1_bi_dx n … H) -H //
qed.

(*** yle_plus1_to_minus_inj1 *)
lemma yle_plus_sn_sn_minus1_dx (n) (x) (z):
      yinj_nat n + x ≤ z → x ≤ z - n.
/2 width=1 by yle_plus_sn_dx_minus1_dx/ qed.

(*** yle_plus2_to_minus_inj2 *)
lemma yle_plus_dx_dx_minus1_sn (o) (x) (y):
      x ≤ y + yinj_nat o → x - o ≤ y.
/2 width=1 by yle_minus1_bi_dx/ qed.

(*** yle_plus2_to_minus_inj1 *)
lemma yle_plus_dx_sn_minus1_sn (o) (x) (y):
      x ≤ yinj_nat o + y → x - o ≤ y.
/2 width=1 by yle_plus_dx_dx_minus1_sn/ qed.

(* Destructions with yminus and yplus ***************************************)

(*** yplus_minus_comm_inj *)
lemma yminus1_plus_comm_23 (n) (x) (z):
      yinj_nat n ≤ x → x - n + z = x + z - n.
#n #x @(ynat_split_nat_inf … x) -x //
#m #z #Hnm @(ynat_split_nat_inf … z) -z
[ #o <yminus1_inj_sn <yplus_inj_bi <yplus_inj_bi <yminus1_inj_sn
  <nminus_plus_comm_23 /2 width=1 by yle_inv_inj_bi/
| <yplus_inf_dx <yplus_inf_dx //
]
qed-.

(*** yplus_minus_assoc_inj *)
lemma yplus_minus1_assoc (o) (x) (y):
      yinj_nat o ≤ y → x + y - o = x + (y - o).
#o #x @(ynat_split_nat_inf … x) -x //
#m #y @(ynat_split_nat_inf … y) -y
[ #n #Hon <yminus1_inj_sn <yplus_inj_bi <yplus_inj_bi
  <nplus_minus_assoc /2 width=1 by yle_inv_inj_bi/
| #_ <yminus1_inf_sn //
]
qed-.

(*** yplus_minus_assoc_comm_inj *)
lemma yminus1_assoc_comm_23 (n) (o) (x):
      n ≤ o → x + yinj_nat n - o = x - (o - n).
#n #o #x @(ynat_split_nat_inf … x) -x
[ #m #Hno <yminus1_inj_sn <yplus_inj_bi <yminus1_inj_sn
  <nminus_assoc_comm_23 //
| #_ <yminus1_inf_sn <yplus_inf_sn // 
]
qed-.

(* Inversions with yminus and yplus *****************************************)

(*** yminus_plus *)
lemma yplus_minus1_sn_refl_sn (n) (x):
      yinj_nat n ≤ x → x = x - n + yinj_nat n.
/2 width=1 by yminus1_plus_comm_23/ qed-.

lemma yplus_minus1_dx_refl_sn (n) (x):
      yinj_nat n ≤ x → x = yinj_nat n + (x - n).
/2 width=1 by yplus_minus1_sn_refl_sn/ qed-.

(*** yplus_inv_minus *)
lemma eq_inv_yplus_bi_inj_md (n1) (m2) (x1) (y2):
      yinj_nat n1 ≤ x1 → x1 + yinj_nat m2 = yinj_nat n1 + y2 →
      ∧∧ x1 - n1 = y2 - m2 & yinj_nat m2 ≤ y2.
#n1 #m2 #x1 #y2 #Hnx1 #H12
lapply (yle_plus_bi_dx (yinj_nat m2) … Hnx1) >H12 #H
lapply (yle_inv_plus_bi_sn_inj … H) -H #Hmy2
generalize in match H12; -H12 (**) (* rewrite in hyp *)
>(yplus_minus1_sn_refl_sn … Hmy2) in ⊢ (%→?); <yplus_assoc #H
lapply (eq_inv_yplus_bi_dx_inj … H) -H
>(yplus_minus1_dx_refl_sn … Hnx1) in ⊢ (%→?); -Hnx1 #H
lapply (eq_inv_yplus_bi_sn_inj … H) -H #H12
/2 width=1 by conj/
qed-.

(*** yle_inv_plus_inj2 yle_inv_plus_inj_dx *)
lemma yle_inv_plus_sn_inj_dx (n) (x) (z):
      x + yinj_nat n ≤ z →
      ∧∧ x ≤ z - n & yinj_nat n ≤ z.
/3 width=3 by yle_plus_sn_dx_minus1_dx, yle_trans, conj/
qed-.

(*** yle_inv_plus_inj1 *)
lemma yle_inv_plus_sn_inj_sn (n) (x) (z):
      yinj_nat n + x ≤ z →
      ∧∧ x ≤ z - n & yinj_nat n ≤ z.
/2 width=1 by yle_inv_plus_sn_inj_dx/ qed-.
