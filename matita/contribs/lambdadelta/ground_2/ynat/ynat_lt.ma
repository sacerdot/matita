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

include "ground_2/ynat/ynat_le.ma".

(* NATURAL NUMBERS WITH INFINITY ********************************************)

(* strict order relation *)
inductive ylt: relation ynat ≝
| ylt_inj: ∀m,n. m < n → ylt m n
| ylt_Y  : ∀m:nat. ylt m (∞)
.

interpretation "ynat 'less than'" 'lt x y = (ylt x y).

(* Basic inversion lemmas ***************************************************)

fact ylt_inv_inj2_aux: ∀x,y. x < y → ∀n. y = yinj n →
                       ∃∃m. m < n & x = yinj m.
#x #y * -x -y
[ #x #y #Hxy #n #Hy elim (le_inv_S1 … Hxy) -Hxy
  #m #Hm #H destruct /3 width=3 by le_S_S, ex2_intro/
| #x #n #Hy destruct
]
qed-.

lemma ylt_inv_inj2: ∀x,n. x < yinj n →
                    ∃∃m. m < n & x = yinj m.
/2 width=3 by ylt_inv_inj2_aux/ qed-.

lemma ylt_inv_inj: ∀m,n. yinj m < yinj n → m < n.
#m #n #H elim (ylt_inv_inj2 … H) -H
#x #Hx #H destruct //
qed-.

fact ylt_inv_Y2_aux: ∀x,y. x < y → y = ∞ → ∃m. x = yinj m.
#x #y * -x -y /2 width=2 by ex_intro/
qed-.

lemma ylt_inv_Y2: ∀x. x < ∞ → ∃m. x = yinj m.
/2 width=3 by ylt_inv_Y2_aux/ qed-.

(* Inversion lemmas on successor ********************************************)

fact ylt_inv_succ1_aux: ∀x,y. x < y → ∀m. x = ⫯m → ∃∃n. m < n & y = ⫯n.
#x #y * -x -y
[ #x #y #Hxy #m #H elim (ysucc_inv_inj_sn … H) -H
  #n #H1 #H2 destruct elim (le_inv_S1 … Hxy) -Hxy
  #m #Hnm #H destruct
  @(ex2_intro … m) /2 width=1 by ylt_inj/ (**) (* explicit constructor *)
| #x #y #H elim (ysucc_inv_inj_sn … H) -H
  #m #H #_ destruct
  @(ex2_intro … (∞)) /2 width=1 by/ (**) (* explicit constructor *)
]
qed-.

lemma ylt_inv_succ1: ∀m,y.  ⫯m < y → ∃∃n. m < n & y = ⫯n.
/2 width=3 by ylt_inv_succ1_aux/ qed-.

lemma yle_inv_succ: ∀m,n. ⫯m < ⫯n → m < n.
#m #n #H elim (ylt_inv_succ1 … H) -H
#x #Hx #H destruct //
qed-.

fact ylt_inv_succ2_aux: ∀x,y. x < y → ∀n. y = ⫯n → x ≤ n.
#x #y * -x -y
[ #x #y #Hxy #m #H elim (ysucc_inv_inj_sn … H) -H
  #n #H1 #H2 destruct /3 width=1 by yle_inj, le_S_S_to_le/
| #x #n #H lapply (ysucc_inv_Y_sn … H) -H //
]
qed-.

lemma ylt_inv_succ2: ∀m,n. m < ⫯n → m ≤ n.
/2 width=3 by ylt_inv_succ2_aux/ qed-.

(* inversion and forward lemmas on yle **************************************)

lemma lt_fwd_le: ∀m:ynat. ∀n:ynat. m < n → m ≤ n.
#m #n * -m -n /3 width=1 by yle_pred_sn, yle_inj, yle_Y/
qed-.

lemma ylt_yle_false: ∀m:ynat. ∀n:ynat. m < n → n ≤ m → ⊥.
#m #n * -m -n
[ #m #n #Hmn #H lapply (yle_inv_inj … H) -H
  #H elim (lt_refl_false n) /2 width=3 by le_to_lt_to_lt/
| #m #H lapply (yle_inv_Y1 … H) -H
  #H destruct
]
qed-.

(* Properties on yle ********************************************************)

lemma yle_to_ylt_or_eq: ∀m:ynat. ∀n:ynat. m ≤ n → m < n ∨ m = n.
#m #n * -m -n
[ #m #n #Hmn elim (le_to_or_lt_eq … Hmn) -Hmn
  /3 width=1 by or_introl, ylt_inj/
| * /2 width=1 by or_introl, ylt_Y/
]
qed-.

lemma ylt_yle_trans: ∀x:ynat. ∀y:ynat. ∀z:ynat. y ≤ z → x < y → x < z.
#x #y #z * -y -z
[ #y #z #Hyz #H elim (ylt_inv_inj2 … H) -H
  #m #Hm #H destruct /3 width=3 by ylt_inj, lt_to_le_to_lt/
| #y * //
]
qed-.

lemma yle_ylt_trans: ∀x:ynat. ∀y:ynat. ∀z:ynat. y < z → x ≤ y → x < z.
#x #y #z * -y -z
[ #y #z #Hyz #H elim (yle_inv_inj2 … H) -H
  #m #Hm #H destruct /3 width=3 by ylt_inj, le_to_lt_to_lt/
| #y #H elim (yle_inv_inj2 … H) -H //
]
qed-.

(* Main properties **********************************************************)

theorem ylt_trans: Transitive … ylt.
#x #y * -x -y
[ #x #y #Hxy * //
  #z #H lapply (ylt_inv_inj … H) -H
  /3 width=3 by transitive_lt, ylt_inj/ (**) (* full auto too slow *)
| #x #z #H elim (ylt_yle_false … H) //
]
qed-. 
