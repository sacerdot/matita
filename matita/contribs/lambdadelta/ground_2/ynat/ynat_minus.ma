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

(* subtraction *)
definition yminus: ynat → ynat → ynat ≝ λx,y. match y with
[ yinj n ⇒ ypred^n x
| Y      ⇒ yinj 0
].

interpretation "ynat minus" 'minus x y = (yminus x y).

(* Basic properties *********************************************************)

lemma yminus_inj: ∀n,m. yinj m - yinj n = yinj (m - n).
#n elim n -n /2 width=3 by trans_eq/
qed.

lemma yminus_Y_inj: ∀n. ∞ - yinj n = ∞.
#n elim n -n // normalize
#n #IHn >IHn //
qed.

(* Properties on predecessor ************************************************)

lemma yminus_SO2: ∀m. m - 1 = ⫰m.
* //
qed.

(* Properties on successor **************************************************)

lemma yminus_succ: ∀n,m. ⫯m - ⫯n = m - n.
* // #n * [2: >yminus_Y_inj // ]
#m >yminus_inj //
qed. 

(* Properties on order ******************************************************)

lemma yle_minus_sn: ∀n,m. m - n ≤ m.
* // #n * /2 width=1 by yle_inj/
qed.

lemma yle_to_minus: ∀m:ynat. ∀n:ynat. m ≤ n → m - n = 0.
#m #n * -m -n /3 width=3 by eq_minus_O, eq_f/
qed-.

lemma yminus_to_le: ∀n:ynat. ∀m:ynat. m - n = 0 → m ≤ n.
* // #n *
[ #m >yminus_inj #H lapply (yinj_inj … H) -H (**) (* destruct lemma needed *)
  /2 width=1 by yle_inj/
| >yminus_Y_inj #H destruct
]
qed.
