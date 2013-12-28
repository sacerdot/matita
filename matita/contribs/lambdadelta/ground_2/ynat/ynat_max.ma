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

lemma ymax_pre_dx: ∀x,y. x ≤ y → x - y + y = y.
#x #y * -x -y //
#x #y #Hxy >yminus_inj >(eq_minus_O … Hxy) -Hxy //
qed-.

lemma ymax_pre_sn: ∀x,y. y ≤ x → x - y + y = x.
#x #y * -x -y
[ #x #y #Hxy >yminus_inj /3 width=3 by plus_minus, eq_f/
| * //
]
qed-.

lemma ymax_pre_i_dx: ∀y,x. y ≤ x - y + y.
// qed.

lemma ymax_pre_i_sn: ∀y,x. x ≤ x - y + y.
* // #y * /2 width=1 by yle_inj/
qed.

lemma ymax_pre_e: ∀x,z. x ≤ z → ∀y. y ≤ z → x - y + y ≤ z.
#x #z #Hxz #y #Hyz elim (yle_split x y)
[ #Hxy >(ymax_pre_dx … Hxy) -x //
| #Hyx >(ymax_pre_sn … Hyx) -y //
]
qed.

lemma ymax_pre_dx_comm: ∀x,y. x ≤ y → y + (x - y) = y.
/2 width=1 by ymax_pre_dx/ qed-.

lemma ymax_pre_sn_comm: ∀x,y. y ≤ x → y + (x - y) = x.
/2 width=1 by ymax_pre_sn/ qed-.

lemma ymax_pre_i_dx_comm: ∀y,x. y ≤ y + (x - y).
// qed.

lemma ymax_pre_i_sn_comm: ∀y,x. x ≤ y + (x - y).
/2 width=1 by ymax_pre_i_sn/ qed.

lemma ymax_pre_e_comm: ∀x,z. x ≤ z → ∀y. y ≤ z → y + (x - y) ≤ z.
/2 width=1 by ymax_pre_e/ qed.
