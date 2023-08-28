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

include "ground/arith/nat_le_plus.ma".
include "ground/arith/nat_lt.ma".

(* STRICT ORDER FOR NON-NEGATIVE INTEGERS ***********************************)

(* Constructions with nplus *************************************************)

(*** monotonic_lt_plus_l *)
lemma nlt_plus_bi_dx (m) (n1) (n2): n1 < n2 → n1 + m < n2 + m.
#m #n1 #n2 #H
@nlt_i >nplus_succ_sn /2 width=1 by nle_plus_bi_dx/
qed.

(*** monotonic_lt_plus_r *)
lemma nlt_plus_bi_sn (m) (n1) (n2): n1 < n2 → m + n1 < m + n2.
#m #n1 #n2 #H
@nlt_i >nplus_succ_dx /2 width=1 by nle_plus_bi_sn/
qed.

lemma nlt_plus_dx_dx (o) (m) (n): m < n → m < n + o.
/2 width=1 by nle_plus_dx_dx/ qed.

lemma nlt_plus_dx_sn (o) (m) (n) : m < n → m < o + n.
/2 width=1 by nle_plus_dx_sn/ qed.

lemma nlt_succ_plus_dx_refl_sn (m) (n): m < (⁤↑(m + n)).
/2 width=1/ qed.

(* Inversions with nplus ****************************************************)

(*** lt_plus_to_lt_l *)
lemma nlt_inv_plus_bi_dx (m) (n1) (n2): n1 + m < n2 + m → n1 < n2.
/2 width=2 by nle_inv_plus_bi_dx/ qed-.

(*** lt_plus_to_lt_r *)
lemma nlt_inv_plus_bi_sn (m) (n1) (n2): m + n1 < m + n2 → n1 < n2.
/2 width=2 by nle_inv_plus_bi_sn/ qed-.
