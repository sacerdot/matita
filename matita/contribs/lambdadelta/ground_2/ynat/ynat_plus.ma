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

include "ground_2/ynat/ynat_lt.ma".

(* NATURAL NUMBERS WITH INFINITY ********************************************)

(* addition *)
definition yplus: ynat → ynat → ynat ≝ λx,y. match y with
[ yinj n ⇒ ysucc^n x
| Y      ⇒ Y
].

interpretation "ynat plus" 'plus x y = (yplus x y).

lemma yplus_O2: ∀m:ynat. m + 0 = m.
// qed.

lemma yplus_S2: ∀m:ynat. ∀n. m + S n = ↑(m + n).
// qed.

lemma yplus_Y2: ∀m:ynat. m + (∞) = ∞.
// qed.

(* Properties on successor **************************************************)

lemma yplus_succ2: ∀m,n. m + ↑n = ↑(m + n).
#m * //
qed.

lemma yplus_succ1: ∀m,n. ↑m + n = ↑(m + n).
#m * // #n elim n -n //
qed.

lemma yplus_succ_swap: ∀m,n. m + ↑n = ↑m + n.
// qed.

lemma yplus_SO2: ∀m. m + 1 = ↑m.
* //
qed.

(* Basic properties *********************************************************)

lemma yplus_inj: ∀n,m. yinj m + yinj n = yinj (m + n).
#n elim n -n //
#n #IHn #m >(yplus_succ2 ? n) >IHn -IHn
<plus_n_Sm //
qed.

lemma yplus_Y1: ∀m. ∞ + m = ∞.
* // #m elim m -m //
qed.

lemma yplus_comm: commutative … yplus.
* [ #m ] * [1,3: #n ] //
qed.

lemma yplus_assoc: associative … yplus.
#x #y * // #z cases y -y
[ #y >yplus_inj whd in ⊢ (??%%); <iter_plus //
| >yplus_Y1 //
]
qed.

lemma yplus_O1: ∀n:ynat. 0 + n = n.
#n >yplus_comm // qed.

lemma yplus_comm_23: ∀x,y,z. x + z + y = x + y + z.
#x #y #z >yplus_assoc //
qed.

lemma yplus_comm_24: ∀x1,x2,x3,x4. x1 + x4 + x3 + x2 = x1 + x2 + x3 + x4.
#x1 #x2 #x3 #x4
>yplus_assoc >yplus_assoc >yplus_assoc >yplus_assoc
/2 width=1 by eq_f2/
qed.

lemma yplus_assoc_23: ∀x1,x2,x3,x4. x1 + x2 + (x3 + x4) = x1 + (x2 + x3) + x4.  
#x1 #x2 #x3 #x4 >yplus_assoc >yplus_assoc
/2 width=1 by eq_f2/
qed.

(* Inversion lemmas on successor *********************************************)

lemma yplus_inv_succ_lt_dx: ∀x,y,z:ynat. 0 < y → x + y = ↑z → x + ↓y = z.
#x #y #z #H <(ylt_inv_O1 y) // >yplus_succ2
/2 width=1 by ysucc_inv_inj/
qed-.

lemma yplus_inv_succ_lt_sn: ∀x,y,z:ynat. 0 < x → x + y = ↑z → ↓x + y = z.
#x #y #z #H <(ylt_inv_O1 x) // >yplus_succ1
/2 width=1 by ysucc_inv_inj/

qed-.

(* Inversion lemmas on order ************************************************)

lemma yle_inv_plus_dx: ∀x,y. x ≤ y → ∃z. x + z = y.
#x #y #H elim H -x -y /2 width=2 by ex_intro/
#m #n #H @(ex_intro … (yinj (n-m))) (**) (* explicit constructor *)
/3 width=1 by plus_minus, eq_f/
qed-.

lemma yle_inv_plus_sn: ∀x,y. x ≤ y → ∃z. z + x = y.
#x #y #H elim (yle_inv_plus_dx … H) -H
/2 width=2 by ex_intro/
qed-.

(* Basic inversion lemmas ***************************************************)

lemma yplus_inv_inj: ∀z,y,x. x + y = yinj z →
                     ∃∃m,n. m + n = z & x = yinj m & y = yinj n.
#z * [2: normalize #x #H destruct ]
#y * [2: >yplus_Y1 #H destruct ]
/3 width=5 by yinj_inj, ex3_2_intro/
qed-.

lemma yplus_inv_O: ∀x,y:ynat. x + y = 0 → x = 0 ∧ y = 0.
#x #y #H elim (yplus_inv_inj … H) -H
#m * /2 width=1 by conj/ #n <plus_n_Sm #H destruct
qed-.

lemma discr_yplus_xy_x: ∀x,y. x + y = x → x = ∞ ∨ y = 0.
* /2 width=1 by or_introl/
#x elim x -x /2 width=1 by or_intror/
#x #IHx * [2: >yplus_Y2 #H destruct ]
#y <ysucc_inj >yplus_succ1 #H
lapply (ysucc_inv_inj … H) -H #H
elim (IHx … H) -IHx -H /2 width=1 by or_introl, or_intror/
qed-.

lemma discr_yplus_x_xy: ∀x,y. x = x + y → x = ∞ ∨ y = 0.
/2 width=1 by discr_yplus_xy_x/ qed-.

lemma yplus_inv_monotonic_dx_inj: ∀z,x,y. x + yinj z = y + yinj z → x = y.
#z @(nat_ind_plus … z) -z /3 width=2 by ysucc_inv_inj/
qed-.

lemma yplus_inv_monotonic_dx: ∀z,x,y. z < ∞ → x + z = y + z → x = y.
#z #x #y #H elim (ylt_inv_Y2 … H) -H /2 width=2 by yplus_inv_monotonic_dx_inj/ 
qed-.

lemma yplus_inv_Y2: ∀x,y. x + y = ∞ → x = ∞ ∨ y = ∞.
* /2 width=1 by or_introl/ #x * // #y >yplus_inj #H destruct 
qed-.

lemma yplus_inv_monotonic_23: ∀z,x1,x2,y1,y2. z < ∞ →
                              x1 + z + y1 = x2 + z + y2 → x1 + y1 = x2 + y2. 
#z #x1 #x2 #y1 #y2 #Hz #H @(yplus_inv_monotonic_dx z) //
>yplus_comm_23 >H -H //
qed-.

(* Inversion lemmas on strict_order *****************************************)

lemma ylt_inv_plus_Y: ∀x,y. x + y < ∞ → x < ∞ ∧ y < ∞.
#x #y #H elim (ylt_inv_Y2 … H) -H
#z #H elim (yplus_inv_inj … H) -H /2 width=1 by conj/
qed-.

lemma ylt_inv_plus_sn: ∀x,y. x < y → ∃∃z. ↑z + x = y & x < ∞.
#x #y #H elim (ylt_inv_le … H) -H
#Hx #H elim (yle_inv_plus_sn … H) -H
/2 width=2 by ex2_intro/
qed-.

lemma ylt_inv_plus_dx: ∀x,y. x < y → ∃∃z. x + ↑z = y & x < ∞.
#x #y #H elim (ylt_inv_plus_sn … H) -H
#z >yplus_comm /2 width=2 by ex2_intro/
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
/3 width=3 by monotonic_yle_plus_dx, monotonic_yle_plus_sn, yle_trans/ qed.

lemma ylt_plus_Y: ∀x,y. x < ∞ → y < ∞ → x + y < ∞.
#x #y #Hx elim (ylt_inv_Y2 … Hx) -Hx
#m #Hm #Hy elim (ylt_inv_Y2 … Hy) -Hy //
qed.

(* Forward lemmas on order **************************************************)

lemma yle_fwd_plus_sn2: ∀x,y,z. x + y ≤ z → y ≤ z.
/2 width=3 by yle_trans/ qed-.

lemma yle_fwd_plus_sn1: ∀x,y,z. x + y ≤ z → x ≤ z.
/2 width=3 by yle_trans/ qed-.

lemma yle_inv_monotonic_plus_dx_inj: ∀x,y:ynat.∀z:nat. x + z ≤ y + z → x ≤ y.
#x #y #z elim z -z /3 width=1 by yle_inv_succ/
qed-.

lemma yle_inv_monotonic_plus_sn_inj: ∀x,y:ynat.∀z:nat. z + x ≤ z + y → x ≤ y.
/2 width=2 by yle_inv_monotonic_plus_dx_inj/ qed-.

lemma yle_inv_monotonic_plus_dx: ∀x,y,z. z < ∞ → x + z ≤ y + z → x ≤ y.
#x #y #z #Hz elim (ylt_inv_Y2 … Hz) -Hz #m #H destruct
/2 width=2 by yle_inv_monotonic_plus_sn_inj/
qed-.

lemma yle_inv_monotonic_plus_sn: ∀x,y,z. z < ∞ → z + x ≤ z + y → x ≤ y.
/2 width=3 by yle_inv_monotonic_plus_dx/ qed-.

lemma yle_fwd_plus_ge: ∀m1,m2:nat. m2 ≤ m1 → ∀n1,n2:ynat. m1 + n1 ≤ m2 + n2 → n1 ≤ n2.
#m1 #m2 #Hm12 #n1 #n2 #H
lapply (monotonic_yle_plus … Hm12 … H) -Hm12 -H
/2 width=2 by yle_inv_monotonic_plus_sn_inj/
qed-.

lemma yle_fwd_plus_ge_inj: ∀m1:nat. ∀m2,n1,n2:ynat. m2 ≤ m1 → m1 + n1 ≤ m2 + n2 → n1 ≤ n2.
#m2 #m1 #n1 #n2 #H elim (yle_inv_inj2 … H) -H
#x #H0 #H destruct /3 width=4 by yle_fwd_plus_ge, yle_inj/
qed-.

lemma yle_fwd_plus_yge: ∀n2,m1:ynat. ∀n1,m2:nat. m2 ≤ m1 → m1 + n1 ≤ m2 + n2 → n1 ≤ n2.
* // #n2 * /2 width=4 by yle_fwd_plus_ge_inj/
qed-.

(* Properties on strict order ***********************************************)

lemma ylt_plus_dx1_trans: ∀x,z. z < x → ∀y. z < x + y.
/2 width=3 by ylt_yle_trans/ qed.

lemma ylt_plus_dx2_trans: ∀y,z. z < y → ∀x. z < x + y.
/2 width=3 by ylt_yle_trans/ qed.

lemma monotonic_ylt_plus_dx_inj: ∀x,y. x < y → ∀z:nat. x + yinj z < y + yinj z.
#x #y #Hxy #z elim z -z /3 width=1 by ylt_succ/
qed.

lemma monotonic_ylt_plus_sn_inj: ∀x,y. x < y → ∀z:nat. yinj z + x < yinj z + y.
/2 width=1 by monotonic_ylt_plus_dx_inj/ qed.

lemma monotonic_ylt_plus_dx: ∀x,y. x < y → ∀z. z < ∞ → x + z < y + z.
#x #y #Hxy #z #Hz elim (ylt_inv_Y2 … Hz) -Hz
#m #H destruct /2 width=1 by monotonic_ylt_plus_dx_inj/
qed.  

lemma monotonic_ylt_plus_sn: ∀x,y. x < y → ∀z. z < ∞ → z + x < z + y.
/2 width=1 by monotonic_ylt_plus_dx/ qed.

lemma monotonic_ylt_plus_inj: ∀m1,m2. m1 < m2 → ∀n1,n2. yinj n1 ≤ n2 → m1 + n1 < m2 + n2.
/3 width=3 by monotonic_ylt_plus_sn_inj, monotonic_yle_plus_sn, ylt_yle_trans/
qed.

lemma monotonic_ylt_plus: ∀m1,m2. m1 < m2 → ∀n1. n1 < ∞ → ∀n2. n1 ≤ n2 → m1 + n1 < m2 + n2.
#m1 #m2 #Hm12 #n1 #H elim (ylt_inv_Y2 … H) -H #m #H destruct /2 width=1 by monotonic_ylt_plus_inj/
qed.

(* Forward lemmas on strict order *******************************************)

lemma ylt_inv_monotonic_plus_dx: ∀x,y,z. x + z < y + z → x < y.
* [2: #y #z >yplus_comm #H elim (ylt_inv_Y1 … H) ]
#x * // #y * [2: #H elim (ylt_inv_Y1 … H) ]
/4 width=3 by ylt_inv_inj, ylt_inj, lt_plus_to_lt_l/
qed-.

lemma ylt_fwd_plus_ge: ∀m1,m2. m2 ≤ m1 → ∀n1,n2. m1 + n1 < m2 + n2 → n1 < n2.
#m1 #m2 #Hm12 #n1 #n2 #H elim (ylt_fwd_gen … H)
#x #H0 elim (yplus_inv_inj … H0) -H0
#y #z #_ #H2 #H3 destruct -x
elim (yle_inv_inj2 … Hm12)
#x #_ #H0 destruct
lapply (monotonic_ylt_plus … H … Hm12) -H -Hm12
/2 width=2 by ylt_inv_monotonic_plus_dx/
qed-.

(* Properties on predeccessor ***********************************************)

lemma yplus_pred1: ∀x,y:ynat. 0 < x → ↓x + y = ↓(x+y).
#x * // #y elim y -y // #y #IH #Hx
>yplus_S2 >yplus_S2 >IH -IH // >ylt_inv_O1
/2 width=1 by ylt_plus_dx1_trans/
qed-.

lemma yplus_pred2: ∀x,y:ynat. 0 < y → x + ↓y = ↓(x+y).
/2 width=1 by yplus_pred1/ qed-.
