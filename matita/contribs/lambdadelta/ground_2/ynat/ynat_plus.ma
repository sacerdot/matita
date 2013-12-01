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

lemma yplus_O_sn: ∀n:ynat. 0 + n = n.
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

(* Forward lemmas on order **************************************************)

lemma yle_fwd_plus_sn2: ∀x,y,z. x + y ≤ z → y ≤ z.
/2 width=3 by yle_trans/ qed-.

lemma yle_fwd_plus_sn1: ∀x,y,z. x + y ≤ z → x ≤ z.
/2 width=3 by yle_trans/ qed-.
