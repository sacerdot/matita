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

include "ground/arith/ynat_le.ma".
include "ground/arith/ynat_lt.ma".

(* STRICT ORDER FOR NON-NEGATIVE INTEGERS WITH INFINITY *********************)

(* Constructions with yle ***************************************************)

(*** yle_split_eq *)
lemma yle_split_lt_eq (x) (y):
      x ≤ y → ∨∨ x < y | x = y.
#x #y * -x -y
[ #m #n #Hmn elim (nle_split_lt_eq … Hmn) -Hmn
  /3 width=1 by or_introl, ylt_inj/
| #x @(ynat_split_nat_inf … x) -x
 /2 width=1 by or_introl, ylt_inf/
]
qed-.

(*** ylt_split *)
lemma ynat_split_lt_ge (x) (y): ∨∨ x < y | y ≤ x.
#x #y elim (ynat_split_le_ge x y) /2 width=1 by or_intror/
#H elim (yle_split_lt_eq … H) -H /2 width=1 by or_introl, or_intror/
qed-.

(*** ylt_split_eq *)
lemma ynat_split_lt_eq_gt (x) (y): ∨∨ x < y | y = x | y < x.
#x #y elim (ynat_split_lt_ge x y) /2 width=1 by or3_intro0/
#H elim (yle_split_lt_eq … H) -H /2 width=1 by or3_intro1, or3_intro2/
qed-.

(*** ylt_yle_trans *)
lemma ylt_yle_trans (x) (y) (z): y ≤ z → x < y → x < z.
#x #y #z * -y -z
[ #n #o #Hno #H elim (ylt_inv_inj_dx … H) -H
  #m #Hmn #H destruct /3 width=3 by ylt_inj, nlt_nle_trans/
| #y /2 width=2 by ylt_des_lt_inf_dx/
]
qed-.

(*** yle_ylt_trans *)
lemma yle_ylt_trans (x) (y) (z): y < z → x ≤ y → x < z.
#x #y #z * -y -z
[ #n #o #Hno #H elim (yle_inv_inj_dx … H) -H
  #m #Hmn #H destruct /3 width=3 by ylt_inj, nle_nlt_trans/
| #n #H elim (yle_inv_inj_dx … H) -H #m #_ #H destruct //
]
qed-.

(*** le_ylt_trans *)
lemma nle_ylt_trans (m) (n) (z):
      m ≤ n → yinj_nat n < z → yinj_nat m < z.
/3 width=3 by yle_ylt_trans, yle_inj/ qed-.

(* Inversions with yle ******************************************************)

(* ylt_yle_false *)
lemma ylt_ge_false (x) (y): x < y → y ≤ x → ⊥.
/3 width=4 by yle_ylt_trans, ylt_inv_refl/ qed-.

(* Destructions with yle ****************************************************)

(*** ylt_fwd_le *)
lemma ylt_des_le (x) (y): x < y → x ≤ y.
#x #y * -x -y
/3 width=1 by nlt_des_le, yle_inj/
qed-.

(* Eliminations *************************************************************)

(*** ynat_ind_lt_le_aux *)
lemma ynat_ind_lt_le_inj_dx (Q:predicate …):
      (∀y. (∀x. x < y → Q x) → Q y) →
      ∀n,x. x ≤ yinj_nat n → Q x.
#Q #IH #n #x #H
elim (yle_inv_inj_dx … H) -H #m #Hmn #H destruct
@(nat_ind_lt_le … Hmn) -Hmn #n0 #IH0
@IH -IH #x #H
elim (ylt_inv_inj_dx … H) -H #m0 #Hmn0 #H destruct
/2 width=1 by/
qed-.

(*** ynat_ind_lt_aux *)
lemma ynat_ind_lt_inj (Q:predicate …):
      (∀y. (∀x. x < y → Q x) → Q y) →
      ∀n. Q (yinj_nat n).
/4 width=2 by ynat_ind_lt_le_inj_dx/ qed-.

(*** ynat_ind_lt *)
lemma ynat_ind_lt (Q:predicate …):
      (∀y. (∀x. x < y → Q x) → Q y) →
      ∀y. Q y.
#Q #IH #y @(ynat_split_nat_inf … y) -y
[ /4 width=1 by ynat_ind_lt_inj/
| @IH #x #H
  elim (ylt_des_gen_sn … H) -H #m #H destruct
  /4 width=1 by ynat_ind_lt_inj/
]
qed-.
