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

fact ymin_pre_dx_aux: ∀x,y. y ≤ x → x - (x - y) ≤ y.
#x #y * -x -y
[ #x #y #Hxy >yminus_inj
 /3 width=4 by yle_inj, monotonic_le_minus_l/
| * //
]
qed-.

lemma ymin_pre_sn: ∀x,y. x ≤ y → x - (x - y) = x.
#x #y * -x -y //
#x #y #Hxy >yminus_inj >(eq_minus_O … Hxy) -Hxy //
qed-.

lemma ymin_pre_i_dx: ∀x,y. x - (x - y) ≤ y.
#x #y elim (yle_split x y) /2 width=1 by ymin_pre_dx_aux/
#Hxy >(ymin_pre_sn … Hxy) //
qed.

lemma ymin_pre_i_sn: ∀x,y. x - (x - y) ≤ x.
// qed.

lemma ymin_pre_dx: ∀x,y. y ≤ yinj x → yinj x - (yinj x - y) = y.
#x #y #H elim (yle_inv_inj2 … H) -H
#z #Hzx #H destruct >yminus_inj
/3 width=4 by minus_le_minus_minus_comm, eq_f/
qed-.

lemma ymin_pre_e: ∀z,x. z ≤ yinj x → ∀y. z ≤ y →
                  z ≤ yinj x - (yinj x - y).
#z #x #Hzx #y #Hzy elim (yle_split x y)
[ #H >(ymin_pre_sn … H) -y //
| #H >(ymin_pre_dx … H) -x //
]
qed.
