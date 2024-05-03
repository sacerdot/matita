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

include "ground/arith/nat_le.ma".
include "ground/arith/ynat_nat.ma".

(* ORDER FOR NON-NEGATIVE INTEGERS WITH INFINITY ****************************)

(*** yle *)
inductive yle: relation ynat ≝
| yle_inj: ∀m,n. m ≤ n → yle (yinj_nat m) (yinj_nat n)
| yle_inf: ∀x. yle x (∞)
.

interpretation
  "less equal (non-negative integers with infinity)"
  'leq x y = (yle x y).

(* Basic inversions *********************************************************)

(*** yle_inv_inj2 *)
lemma yle_inv_inj_dx (x) (n):
      x ≤ yinj_nat n →
      ∃∃m. m ≤ n & x = yinj_nat m.
#x #n0 @(insert_eq_1 … (yinj_nat n0))
#y #H elim H -x -y
[ #m #n #Hmn #H
  lapply (eq_inv_yinj_nat_bi … H) -H #H destruct
  /2 width=3 by ex2_intro/
| #x #H
  elim (eq_inv_yinj_nat_inf … H)
]
qed-.

(*** yle_inv_inj *)
lemma yle_inv_inj_bi (m) (n):
      yinj_nat m ≤ yinj_nat n → m ≤ n.
#m #n #H
elim (yle_inv_inj_dx … H) -H #x #Hxn #H
lapply (eq_inv_yinj_nat_bi … H) -H #H destruct //
qed-.

(*** yle_inv_O2 *)
lemma yle_inv_zero_dx (x):
      x ≤ 𝟎 → 𝟎 = x.
#x #H
elim (yle_inv_inj_dx ? (𝟎) H) -H #m #Hm #H destruct
<(nle_inv_zero_dx … Hm) -m //
qed-.

(*** yle_inv_Y1 *)
lemma yle_inv_inf_sn (y): ∞ ≤ y → ∞ = y.
#y @(insert_eq_1 … (∞))
#x #H elim H -x -y //
#m #n #_ #H
elim (eq_inv_inf_yinj_nat … H)
qed-.

(*** yle_antisym *)
lemma yle_antisym (x) (y):
      x ≤ y → y ≤ x → x = y.
#x #y #H elim H -x -y
[ #m #n #Hmn #Hnm
  <(nle_antisym … Hmn) -Hmn /2 width=1 by yle_inv_inj_bi/
| /2 width=1 by yle_inv_inf_sn/
]
qed-.

(* Basic constructions ******************************************************)

(*** le_O1 *)
lemma yle_zero_sn (y): 𝟎 ≤ y.
#y @(ynat_split_nat_inf … y) -y
/2 width=1 by yle_inj/
qed.

(*** yle_refl *)
lemma yle_refl: reflexive … yle.
#x @(ynat_split_nat_inf … x) -x
/2 width=1 by yle_inj, yle_inf, nle_refl/
qed.

(*** yle_split *)
lemma ynat_split_le_ge (x) (y):
      ∨∨ x ≤ y | y ≤ x.
#x @(ynat_split_nat_inf … x) -x
[| /2 width=1 by or_intror/ ]
#m #y @(ynat_split_nat_inf … y) -y
[| /3 width=1 by yle_inf, or_introl/ ]
#n elim (nat_split_le_ge m n)
/3 width=1 by yle_inj, or_introl, or_intror/
qed-.

(* Main constructions *******************************************************)

(*** yle_trans *)
theorem yle_trans: Transitive … yle.
#x #y * -x -y
[ #m #n #Hxy #z @(ynat_split_nat_inf … z) -z //
  /4 width=3 by yle_inv_inj_bi, nle_trans, yle_inj/
| #x #z #H <(yle_inv_inf_sn … H) -H //
]
qed-.
