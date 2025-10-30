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

include "ground/arith/nat_le_minus_plus.ma".
include "ground/arith/nat_lt_minus.ma".

(* STRICT ORDER FOR NON-NEGATIVE INTEGERS ***********************************)

(* Constructions with nminus and nplus **************************************)

(*** lt_plus_to_minus *)
lemma nlt_minus_sx (o) (m) (n): m ≤ n → n < o + m → n - m < o.
#o #m #n #Hmn #Ho
lapply (nle_minus_sx_sx … Ho) -Ho
<nminus_succ_sx //
qed.

(*** lt_plus_to_minus_r *)
lemma nlt_minus_dx (o) (m) (n): m + o < n → m < n - o.
/2 width=1 by nle_minus_dx_sx/ qed.

(*** lt_inv_plus_l *)
lemma nlt_minus_dx_full (o) (m) (n): m + o < n → ∧∧ o < n & m < n - o.
/3 width=3 by nlt_minus_dx, nle_nlt_trans, conj/ qed-.

(* Inversions with nminus and nplus *****************************************)

(*** lt_minus_to_plus *)
lemma nlt_inv_minus_sx (o) (m) (n): m - o < n → m < n + o.
#o #m #n #Ho
@nle_inv_minus_sx
@(nle_trans … Ho) -Ho //
qed-.

(*** lt_minus_to_plus_r *)
lemma nlt_inv_minus_dx (o) (m) (n): m < n - o → m + o < n.
#o #m #n #Ho
lapply (nle_inv_minus_dx ???? Ho) //
/3 width=2 by nlt_des_minus_dx, nlt_des_le/
qed-.
