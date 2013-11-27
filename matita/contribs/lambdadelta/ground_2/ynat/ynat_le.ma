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

include "ground_2/ynat/ynat_succ.ma".

(* NATURAL NUMBERS WITH INFINITY ********************************************)

(* order relation *)
inductive yle: relation ynat ≝
| yle_inj: ∀m,n. m ≤ n → yle m n
| yle_Y  : ∀m. yle m (∞)
.

interpretation "ynat 'less or equal to'" 'leq x y = (yle x y).

(* Basic inversion lemmas ***************************************************)

fact yle_inv_inj2_aux: ∀x,y. x ≤ y → ∀n. y = yinj n →
                       ∃∃m. m ≤ n & x = yinj m.
#x #y * -x -y
[ #x #y #Hxy #n #Hy destruct /2 width=3 by ex2_intro/
| #x #n #Hy destruct
]
qed-.

lemma yle_inv_inj2: ∀x,n. x ≤ yinj n → ∃∃m. m ≤ n & x = yinj m.
/2 width=3 by yle_inv_inj2_aux/ qed-.

lemma yle_inv_inj: ∀m,n. yinj m ≤ yinj n → m ≤ n.
#m #n #H elim (yle_inv_inj2 … H) -H
#x #Hxn #H destruct //
qed-.

fact yle_inv_O2_aux: ∀m:ynat. ∀x:ynat. m ≤ x → x = 0 → m = 0.
#m #x * -m -x
[ #m #n #Hmn #H destruct /3 width=1 by le_n_O_to_eq, eq_f/
| #m #H destruct
] 
qed-.

lemma yle_inv_O2: ∀m:ynat. m ≤ 0 → m = 0.
/2 width =3 by yle_inv_O2_aux/ qed-.

fact yle_inv_Y1_aux: ∀x,n. x ≤ n → x = ∞ → n = ∞.
#x #n * -x -n //
#x #n #_ #H destruct
qed-.

lemma yle_inv_Y1: ∀n. ∞ ≤ n → n = ∞.
/2 width=3 by yle_inv_Y1_aux/ qed-.

(* Inversion lemmas on successor ********************************************)

fact yle_inv_succ1_aux: ∀x,y. x ≤ y → ∀m. x = ⫯m → ∃∃n. m ≤ n & y = ⫯n.
#x #y * -x -y
[ #x #y #Hxy #m #H elim (ysucc_inv_inj_sn … H) -H
  #n #H1 #H2 destruct elim (le_inv_S1 … Hxy) -Hxy
  #m #Hnm #H destruct
  @(ex2_intro … m) /2 width=1 by yle_inj/ (**) (* explicit constructor *)
| #x #y #H destruct
  @(ex2_intro … (∞)) /2 width=1 by yle_Y/ (**) (* explicit constructor *)
]
qed-.

lemma yle_inv_succ1: ∀m,y.  ⫯m ≤ y → ∃∃n. m ≤ n & y = ⫯n.
/2 width=3 by yle_inv_succ1_aux/ qed-.

lemma yle_inv_succ: ∀m,n. ⫯m ≤ ⫯n → m ≤ n.
#m #n #H elim (yle_inv_succ1 … H) -H
#x #Hx #H destruct //
qed-.

(* Basic properties *********************************************************)

lemma yle_refl: reflexive … yle.
* /2 width=1 by le_n, yle_inj/
qed.

(* Properties on predecessor ************************************************)

lemma yle_pred_sn: ∀m,n. m ≤ n → ⫰m ≤ n.
#m #n * -m -n /3 width=3 by transitive_le, yle_inj/
qed.

lemma yle_refl_pred_sn: ∀x. ⫰x ≤ x.
/2 width=1 by yle_refl, yle_pred_sn/ qed.

(* Properties on successor **************************************************)

lemma yle_succ_dx: ∀m,n. m ≤ n → m ≤ ⫯n.
#m #n * -m -n /3 width=1 by le_S, yle_inj/
qed.

lemma yle_refl_S_dx: ∀x. x ≤ ⫯x.
/2 width=1 by yle_refl, yle_succ_dx/ qed.

(* Main properties **********************************************************)

theorem yle_trans: Transitive … yle.
#x #y * -x -y
[ #x #y #Hxy * //
  #z #H lapply (yle_inv_inj … H) -H
  /3 width=3 by transitive_le, yle_inj/ (**) (* full auto too slow *)
| #x #z #H lapply (yle_inv_Y1 … H) //
]
qed-. 
