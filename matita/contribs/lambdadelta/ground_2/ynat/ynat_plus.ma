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

include "ground_2/ynat/ynat_minus.ma".

(* NATURAL NUMBERS WITH INFINITY ********************************************)

(* addition *)
definition yplus: ynat → ynat → ynat ≝ λx,y. match y with
[ yinj n ⇒ ysucc^n x
| Y      ⇒ Y
].

interpretation "ynat plus" 'plus x y = (yplus x y).

(* Properties on successor **************************************************)

lemma yplus_succ2: ∀m,n. m + ⫯n = ⫯(m + n).
#m * //
qed.

lemma yplus_succ1: ∀m,n. ⫯m + n = ⫯(m + n).
#m * normalize //
qed.

lemma yplus_succ_swap: ∀m,n. m + ⫯n = ⫯m + n.
// qed.

lemma yplus_SO2: ∀m. m + 1 = ⫯m.
* //
qed.

(* Basic properties *********************************************************)

lemma yplus_inj: ∀n,m. yinj m + yinj n = yinj (m + n).
#n elim n -n [ normalize // ]
#n #IHn #m >(yplus_succ2 ? n) >IHn -IHn
<plus_n_Sm //
qed.

lemma yplus_Y1: ∀m. ∞ + m = ∞.
* normalize //
qed.

lemma yplus_comm: commutative … yplus.
* [ #m ] * [1,3: #n ] //
normalize >ysucc_iter_Y //
qed.

lemma yplus_assoc: associative … yplus.
#x #y * // #z cases y -y
[ #y >yplus_inj whd in ⊢ (??%%); <iter_plus //
| >yplus_Y1 //
]
qed.

lemma yplus_O1: ∀n:ynat. 0 + n = n.
#n >yplus_comm // qed.

(* Basic inversion lemmas ***************************************************)

lemma yplus_inv_inj: ∀z,y,x. x + y = yinj z →
                     ∃∃m,n. m + n = z & x = yinj m & y = yinj n.
#z * [2: normalize #x #H destruct ]
#y * [2: >yplus_Y1 #H destruct ]
/3 width=5 by yinj_inj, ex3_2_intro/
qed-.

(* Properties on order ******************************************************)

lemma yle_plus_dx2: ∀n,m. n ≤ m + n.
* //
#n elim n -n //
#n #IHn #m >(yplus_succ2 ? n) @(yle_succ n) // (**) (* full auto fails *)
qed.

lemma yle_plus_dx1: ∀n,m. m ≤ m + n.
// qed.

lemma yle_plus_dx1_trans: ∀x,z. z ≤ x → ∀y. z ≤ x + y.
/2 width=3 by yle_trans/ qed.

lemma yle_plus_dx2_trans: ∀y,z. z ≤ y → ∀x. z ≤ x + y.
/2 width=3 by yle_trans/ qed.

lemma monotonic_yle_plus_dx: ∀x,y. x ≤ y → ∀z. x + z ≤ y + z.
#x #y #Hxy * //
#z elim z -z /3 width=1 by yle_succ/
qed.

lemma monotonic_yle_plus_sn: ∀x,y. x ≤ y → ∀z. z + x ≤ z + y.
/2 width=1 by monotonic_yle_plus_dx/ qed.

lemma monotonic_yle_plus: ∀x1,y1. x1 ≤ y1 → ∀x2,y2. x2 ≤ y2 →
                          x1 + x2 ≤ y1 + y2.
/3 width=3 by monotonic_yle_plus_dx, yle_trans/ qed.

(* Forward lemmas on order **************************************************)

lemma yle_fwd_plus_sn2: ∀x,y,z. x + y ≤ z → y ≤ z.
/2 width=3 by yle_trans/ qed-.

lemma yle_fwd_plus_sn1: ∀x,y,z. x + y ≤ z → x ≤ z.
/2 width=3 by yle_trans/ qed-.

lemma yle_inv_monotonic_plus_dx: ∀x,y:ynat.∀z:nat. x + z ≤ y + z → x ≤ y.
#x #y #z elim z -z /3 width=1 by yle_inv_succ/
qed-.

lemma yle_inv_monotonic_plus_sn: ∀x,y:ynat.∀z:nat. z + x ≤ z + y → x ≤ y.
/2 width=2 by yle_inv_monotonic_plus_dx/ qed-.

lemma yle_fwd_plus_ge: ∀m1,m2:nat. m2 ≤ m1 → ∀n1,n2:ynat. m1 + n1 ≤ m2 + n2 → n1 ≤ n2.
#m1 #m2 #Hm12 #n1 #n2 #H
lapply (monotonic_yle_plus … Hm12 … H) -Hm12 -H
/2 width=2 by yle_inv_monotonic_plus_sn/
qed-.

lemma yle_fwd_plus_ge_inj: ∀m1:nat. ∀m2,n1,n2:ynat. m2 ≤ m1 → m1 + n1 ≤ m2 + n2 → n1 ≤ n2.
#m2 #m1 #n1 #n2 #H elim (yle_inv_inj2 … H) -H
#x #H0 #H destruct /3 width=4 by yle_fwd_plus_ge, yle_inj/
qed-.

(* Forward lemmas on strict order *******************************************)

lemma ylt_inv_monotonic_plus_dx: ∀x,y,z. x + z < y + z → x < y.
* [2: #y #z >yplus_comm #H elim (ylt_inv_Y1 … H) ]
#x * // #y * [2: #H elim (ylt_inv_Y1 … H) ]
/4 width=3 by ylt_inv_inj, ylt_inj, lt_plus_to_lt_l/
qed-.

(* Properties on strict order ***********************************************)

lemma ylt_plus_dx1_trans: ∀x,z. z < x → ∀y. z < x + yinj y.
/2 width=3 by ylt_yle_trans/ qed.

lemma ylt_plus_dx2_trans: ∀y,z. z < y → ∀x. z < yinj x + y.
/2 width=3 by ylt_yle_trans/ qed.

lemma monotonic_ylt_plus_dx: ∀x,y. x < y → ∀z:nat. x + yinj z < y + yinj z.
#x #y #Hxy #z elim z -z /3 width=1 by ylt_succ/
qed.

lemma monotonic_ylt_plus_sn: ∀x,y. x < y → ∀z:nat. yinj z + x < yinj z + y.
/2 width=1 by monotonic_ylt_plus_dx/ qed.

(* Properties on minus ******************************************************)

lemma yplus_minus_inj: ∀m:ynat. ∀n:nat. m + n - n = m.
#m #n elim n -n //
#n #IHn >(yplus_succ2 m n) >(yminus_succ … n) //
qed.

lemma yplus_minus: ∀m,n. m + n - n ≤ m.
#m * //
qed.

(* Forward lemmas on minus **************************************************)

lemma yle_plus1_to_minus_inj2: ∀x,z:ynat. ∀y:nat. x + y ≤ z → x ≤ z - y.
/2 width=1 by monotonic_yle_minus_dx/ qed-.

lemma yle_plus1_to_minus_inj1: ∀x,z:ynat. ∀y:nat. y + x ≤ z → x ≤ z - y.
/2 width=1 by yle_plus1_to_minus_inj2/ qed-.

lemma yle_plus2_to_minus_inj2: ∀x,y:ynat. ∀z:nat. x ≤ y + z → x - z ≤ y.
/2 width=1 by monotonic_yle_minus_dx/ qed-.

lemma yle_plus2_to_minus_inj1: ∀x,y:ynat. ∀z:nat. x ≤ z + y → x - z ≤ y.
/2 width=1 by yle_plus2_to_minus_inj2/ qed-.

lemma yplus_minus_assoc_inj: ∀x:nat. ∀y,z:ynat. x ≤ y → z + (y - x) = z + y - x.
#x *
[ #y * // #z >yminus_inj >yplus_inj >yplus_inj
  /4 width=1 by yle_inv_inj, plus_minus, eq_f/
| >yminus_Y_inj //
]
qed-.

lemma yplus_minus_comm_inj: ∀y:nat. ∀x,z:ynat. y ≤ x → x + z - y = x - y + z.
#y * // #x * //
#z #Hxy >yplus_inj >yminus_inj <plus_minus
/2 width=1 by yle_inv_inj/
qed-.

(* Inversion lemmas on minus ************************************************)

lemma yle_inv_plus_inj2: ∀x,z:ynat. ∀y:nat. x + y ≤ z → x ≤ z - y ∧ y ≤ z.
/3 width=3 by yle_plus1_to_minus_inj2, yle_trans, conj/ qed-.

lemma yle_inv_plus_inj1: ∀x,z:ynat. ∀y:nat. y + x ≤ z → x ≤ z - y ∧ y ≤ z.
/2 width=1 by yle_inv_plus_inj2/ qed-.
