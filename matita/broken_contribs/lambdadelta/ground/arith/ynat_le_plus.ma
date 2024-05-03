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

include "ground/arith/nat_le_plus.ma".
include "ground/arith/ynat_plus.ma".
include "ground/arith/ynat_le_succ.ma".

(* ORDER FOR NON-NEGATIVE INTEGERS WITH INFINITY ****************************)

(* Constructions with yplus *************************************************)

(*** monotonic_yle_plus *)
lemma yle_plus_bi (x1) (x2) (y1) (y2):
      x1 ≤ y1 → x2 ≤ y2 → x1 + x2 ≤ y1 + y2.
#x1 #x2 #y1 #y2 * //
#m1 #n1 #Hmn1 * //
#m2 #n2 #Hmn2 /3 width=1 by nle_plus_bi, yle_inj/
qed.

(*** monotonic_yle_plus_dx *)
lemma yle_plus_bi_dx (z) (x) (y):
      x ≤ y → x + z ≤ y + z.
/2 width=1 by yle_plus_bi/ qed.

(*** monotonic_yle_plus_sn *)
lemma yle_plus_bi_sn (z) (x) (y):
      x ≤ y → z + x ≤ z + y.
/2 width=1 by yle_plus_bi/ qed.

(*** yle_plus_dx1_trans *)
lemma yle_plus_dx_dx (z) (x) (y):
      z ≤ x → z ≤ x + y.
/2 width=1 by yle_plus_bi/ qed.

(*** yle_plus_dx2_trans *)
lemma yle_plus_dx_sn (z) (x) (y):
      z ≤ y → z ≤ x + y.
#z #x #y <yplus_comm
/2 width=3 by yle_plus_dx_dx/
qed.

(*** yle_plus_dx1 *)
lemma yle_plus_dx_dx_refl (x) (y): x ≤ x + y.
/2 width=1 by yle_plus_dx_dx/ qed.

(*** yle_plus_dx2 *)
lemma yle_plus_dx_sn_refl (x) (y): y ≤ x + y.
// qed-.

(* Inversions with yplus ****************************************************)

(*** yle_inv_monotonic_plus_dx_inj *)
lemma yle_inv_plus_bi_dx_inj (o) (x) (y):
      x + yinj_nat o ≤ y + yinj_nat o → x ≤ y.
#o @(nat_ind_succ … o) -o //
#o #IH #x #y >ysucc_inj <yplus_succ_dx <yplus_succ_dx #H
/3 width=1 by yle_inv_succ_bi/
qed-.

(*** yle_inv_monotonic_plus_sn_inj *)
lemma yle_inv_plus_bi_sn_inj (o) (x) (y):
      yinj_nat o + x ≤ yinj_nat o + y → x ≤ y.
/2 width=2 by yle_inv_plus_bi_dx_inj/ qed-.

(* Destructions with yplus **************************************************)

(*** yle_fwd_plus_sn2 *)
lemma yle_des_plus_sn_sn (x) (y) (z):
      x + y ≤ z → y ≤ z.
/2 width=3 by yle_trans/ qed-.

(*** yle_fwd_plus_sn1 *)
lemma yle_des_plus_sn_dx (x) (y) (z):
      x + y ≤ z → x ≤ z.
/2 width=3 by yle_trans/ qed-.

(*** yle_fwd_plus_ge *)
lemma yle_des_plus_bi_sn_inj_bi (m) (n) (x) (y):
      n ≤ m → yinj_nat m + x ≤ yinj_nat n + y → x ≤ y.
#m #n #x #y #Hnm #H
lapply (yle_inj … Hnm) -Hnm #Hnm
lapply (yle_plus_bi … Hnm … H) -Hnm -H
<yplus_assoc <yplus_inj_bi <yplus_assoc <yplus_inj_bi #H
/2 width=2 by yle_inv_plus_bi_sn_inj/
qed-.

(*** yle_fwd_plus_ge_inj *)
lemma yle_des_plus_bi_sn_inj_sn (o) (z) (x) (y):
      z ≤ yinj_nat o → yinj_nat o + x ≤ z + y → x ≤ y.
#m #z #x #y #H elim (yle_inv_inj_dx … H) -H
#n #Hnm #H destruct
/2 width=4 by yle_des_plus_bi_sn_inj_bi/
qed-.

(*** yle_fwd_plus_yge *)
lemma yle_des_plus_bi_sn_inj_md (m1) (m2) (y1) (y2):
      yinj_nat m2 ≤ y1 → y1 + yinj_nat m1 ≤ yinj_nat m2 + y2 → yinj_nat m1 ≤ y2.
#m1 #m2 #y1 #y2 @(ynat_split_nat_inf … y2) -y2 //
#n2 @(ynat_split_nat_inf … y1) -y1
/2 width=4 by yle_des_plus_bi_sn_inj_sn/
qed-.
