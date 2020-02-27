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

include "ground_2/ynat/ynat_plus.ma".

(* NATURAL NUMBERS WITH INFINITY ********************************************)

(* left subtraction *)
definition yminus_sn (x) (y): ynat ≝ ypred^y x.

interpretation "ynat left minus" 'minus x y = (yminus_sn x y).

lemma yminus_O2: ∀m:ynat. m - 0 = m.
// qed.

lemma yminus_S2: ∀m:ynat. ∀n:nat. m - S n = ↓(m - n).
// qed.

(* Basic properties *********************************************************)

lemma yminus_inj: ∀m,n. yinj m - n = yinj (m - n).
#m #n elim n -n //
#n #IH >yminus_S2 >IH -IH >eq_minus_S_pred //
qed.

lemma yminus_Y_inj: ∀n. ∞ - n = ∞.
#n elim n -n //
qed.

lemma yminus_O1: ∀x:nat. yinj 0 - x = 0.
// qed.

lemma yminus_refl: ∀x:nat. yinj x - x = 0.
// qed.

lemma yminus_minus_comm: ∀x:ynat. ∀y,z. x - y - z = x - z - y.
* // qed.

(* Properties on predecessor ************************************************)

lemma yminus_SO2: ∀m:ynat. m - 1 = ↓m.
// qed.

lemma yminus_pred1: ∀x,y. ↓x - y = ↓(x-y).
#x * // #y elim y -y //
qed.

lemma yminus_pred: ∀m:ynat. ∀n. 0 < m → 0 < n → ↓m - ↓n = m - n.
* // #m #n >yminus_inj >yminus_inj
/4 width=1 by ylt_inv_inj, minus_pred_pred, eq_f/
qed-.

(* Properties on successor **************************************************)

lemma yminus_succ: ∀m:ynat. ∀n. ↑m - ↑n = m - n.
* // qed.

lemma yminus_succ1_inj: ∀n:nat. ∀m:ynat. n ≤ m → ↑m - n = ↑(m - n).
#n *
[ #m #Hmn >yminus_inj >yminus_inj
  /4 width=1 by yle_inv_inj, plus_minus, eq_f/
| >yminus_Y_inj //
]
qed-.

lemma yminus_succ2: ∀x:ynat. ∀y. x - ↑y = ↓(x-y).
* //
qed.

(* Properties on order ******************************************************)

lemma yle_minus_sn: ∀m:ynat. ∀n. m - n ≤ m.
* // #n /2 width=1 by yle_inj/
qed.

lemma yle_to_minus: ∀m:ynat. ∀n:nat. m ≤ n → m - n = 0.
*
[ #m #n #H >yminus_inj /4 width=1 by yle_inv_inj, eq_minus_O, eq_f/
| #n #H lapply (yle_inv_Y1 … H) -H #H destruct
]
qed-.

lemma yminus_to_le: ∀m:ynat. ∀n. m - n = 0 → m ≤ n.
* [2: #n >yminus_Y_inj #H destruct ]
#m #n >yminus_inj #H
lapply (yinj_inj … H) -H (**) (* destruct lemma needed *)
/2 width=1 by yle_inj/
qed.

lemma monotonic_yle_minus_dx: ∀x,y. x ≤ y → ∀z. x - z ≤ y - z.
#x #y * /3 width=1 by yle_inj, monotonic_le_minus_l2/
qed.

(* Properties on strict order ***********************************************)

lemma ylt_to_minus: ∀y:ynat. ∀x. yinj x < y → 0 < y - x.
* // #y #x #H >yminus_inj
/4 width=1 by ylt_inj, ylt_inv_inj, lt_plus_to_minus_r/
qed.

lemma yminus_to_lt: ∀y:ynat. ∀x. 0 < y - x → x < y.
* // #y #x >yminus_inj #H 
/4 width=1 by ylt_inv_inj, ylt_inj, lt_minus_to_plus_r/
qed-.

lemma monotonic_ylt_minus_dx: ∀x,y:ynat. x < y → ∀z:nat. z ≤ x → x - z < y - z.
#x #y * -x -y
/4 width=1 by ylt_inj, yle_inv_inj, monotonic_lt_minus_l/
qed.

(* Properties on minus ******************************************************)

lemma yplus_minus: ∀m:ynat. ∀n:nat. m + n - n = m.
#m #n elim n -n //
#n #IHn >(yplus_succ2 m n) >(yminus_succ … n) //
qed.

lemma yminus_plus2: ∀x:ynat. ∀y,z. x - (y + z) = x - y - z.
* // qed.

(* Forward lemmas on minus **************************************************)

lemma yle_plus1_to_minus_inj2: ∀x,z:ynat. ∀y:nat. x + y ≤ z → x ≤ z - y.
#x #z #y #H lapply (monotonic_yle_minus_dx … H y) -H //
qed-.

lemma yle_plus1_to_minus_inj1: ∀x,z:ynat. ∀y:nat. y + x ≤ z → x ≤ z - y.
/2 width=1 by yle_plus1_to_minus_inj2/ qed-.

lemma yle_plus2_to_minus_inj2: ∀x,y:ynat. ∀z:nat. x ≤ y + z → x - z ≤ y.
/2 width=1 by monotonic_yle_minus_dx/ qed-.

lemma yle_plus2_to_minus_inj1: ∀x,y:ynat. ∀z:nat. x ≤ z + y → x - z ≤ y.
/2 width=1 by yle_plus2_to_minus_inj2/ qed-.

lemma yminus_plus (x:ynat) (y:nat): y ≤ x → x = (x-y)+y.
* // #x #y #H >yminus_inj >yplus_inj
/4 width=1 by yle_inv_inj, plus_minus, eq_f/
qed-.

lemma yplus_minus_assoc_inj: ∀x:nat. ∀y,z:ynat. x ≤ y → z + (y - x) = z + y - x.
#x *
[ #y * // #z >yminus_inj >yplus_inj >yplus_inj
  /4 width=1 by yle_inv_inj, plus_minus, eq_f/
| >yminus_Y_inj //
]
qed-.

alias symbol "plus" (instance 5) = "ynat plus".
alias symbol "minus" (instance 4) = "ynat left minus".
alias symbol "minus" (instance 3) = "natural minus".
alias symbol "minus" (instance 2) = "ynat left minus".
alias symbol "leq" (instance 6) = "natural 'less or equal to'".
lemma yplus_minus_assoc_comm_inj: ∀z:ynat. ∀x,y:nat. x ≤ y → z - (y - x) = z + x - y.
* // #z #x #y >yminus_inj >yplus_inj >yminus_inj
/4 width=1 by yle_inv_inj, minus_le_minus_minus_comm, eq_f/
qed-.

lemma yplus_minus_comm_inj: ∀y:nat. ∀x,z:ynat. y ≤ x → x + z - y = x - y + z.
#y * // #x * //
#z #Hxy >yplus_inj >yminus_inj <plus_minus
/2 width=1 by yle_inv_inj/
qed-.

lemma ylt_plus1_to_minus_inj2: ∀x,z:ynat. ∀y:nat. x + y < z → x < z - y.
#x #z #y #H lapply (monotonic_ylt_minus_dx … H y ?) -H //
qed-.

lemma ylt_plus1_to_minus_inj1: ∀x,z:ynat. ∀y:nat. y + x < z → x < z - y.
/2 width=1 by ylt_plus1_to_minus_inj2/ qed-.

lemma ylt_plus2_to_minus_inj2: ∀x,y:ynat. ∀z:nat. z ≤ x → x < y + z → x - z < y.
/2 width=1 by monotonic_ylt_minus_dx/ qed-.

lemma ylt_plus2_to_minus_inj1: ∀x,y:ynat. ∀z:nat. z ≤ x → x < z + y → x - z < y.
/2 width=1 by ylt_plus2_to_minus_inj2/ qed-.

lemma yplus_inv_Y1: ∀x,y. ∞ = x + y → ∨∨ ∞ = x | ∞ = y.
* /2 width=1 by or_introl/ #x * // #y >yplus_inj #H destruct
qed-.

lemma yplus_inv_minus:
      ∀x1,y2:ynat.∀y1,x2:nat.
      y1 ≤ x1 → x1 + x2 = y2 + y1 → ∧∧ x1 - y1 = y2 - x2 & x2 ≤ y2.
*
[ #x1 * [| #y1 #x2 #_ >yplus_inj >yplus_Y1 #H destruct ]
  #y2 #y1 #x2 #H1 >yplus_inj >yplus_inj #H2 >yminus_inj >yminus_inj
  lapply (yle_inv_inj … H1) -H1 #Hyx1
  lapply (yinj_inj … H2) -H2 #Hxy (**) (* destruct lemma needed *)
  /5 width=4 by yle_inj, plus2_le_sn_sn, plus_to_minus_2, conj, eq_f2/
| #y2 #y1 #x2 #_ >yplus_Y1 #H
  elim (yplus_inv_Y1 … H) -H #H destruct /2 width=1 by conj/
]
qed-.

(* Inversion lemmas on minus ************************************************)

lemma yle_inv_plus_inj2: ∀x,z:ynat. ∀y:nat. x + y ≤ z → x ≤ z - y ∧ y ≤ z.
/3 width=3 by yle_plus1_to_minus_inj2, yle_trans, conj/ qed-.

lemma yle_inv_plus_inj1: ∀x,z:ynat. ∀y:nat. y + x ≤ z → x ≤ z - y ∧ y ≤ z.
/2 width=1 by yle_inv_plus_inj2/ qed-.

lemma yle_inv_plus_inj_dx: ∀z,x:ynat. ∀y:nat. x + y ≤ z →
                           ∧∧ x ≤ z - y & y ≤ z.
* [| /2 width=1 by conj/ ]
#z * [| #y >yplus_Y1 #H >(yle_inv_Y1 … H) -z /2 width=1 by conj/ ]
#x #y >yplus_inj #H >yminus_inj
/5 width=2 by yle_inv_inj, yle_inj, le_plus_to_minus_r, le_plus_b, conj/
qed-.
