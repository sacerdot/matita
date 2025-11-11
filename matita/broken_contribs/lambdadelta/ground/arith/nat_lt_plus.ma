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
include "ground/arith/nat_lt_le.ma".

(* STRICT ORDER FOR NON-NEGATIVE INTEGERS ***********************************)

(* Constructions with nplus *************************************************)

(*** monotonic_lt_plus_l *)
lemma nlt_plus_bi_dx (m) (n1) (n2): n1 < n2 → n1 + m < n2 + m.
#m #n1 #n2 #H0
@nlt_le >nplus_succ_sx
/3 width=1 by nlt_inv_le, nle_plus_bi_dx/
qed.

(*** monotonic_lt_plus_r *)
lemma nlt_plus_bi_sx (m) (n1) (n2): n1 < n2 → m + n1 < m + n2.
#m #n1 #n2 #H0
@nlt_le >nplus_succ_dx
/3 width=1 by nlt_inv_le, nle_plus_bi_sx/
qed.

lemma nlt_plus_dx_dx (o) (m) (n): m < n → m < n + o.
/3 width=1 by nlt_inv_le, nle_plus_dx_dx/
qed.

lemma nlt_plus_dx_sx (o) (m) (n) : m < n → m < o + n.
/3 width=1 by nlt_inv_le, nle_plus_dx_sx/
qed.

lemma nlt_succ_plus_dx_refl_sx (m) (n): m < (⁤↑(m + n)).
/2 width=1/
qed.

(* Inversions with nplus ****************************************************)

(*** lt_plus_to_lt_l *)
lemma nlt_inv_plus_bi_dx (m) (n1) (n2): n1 + m < n2 + m → n1 < n2.
#m #n1 #n2 #H0
lapply (nlt_inv_le … H0) -H0 #H0
/3 width=2 by nlt_le, nle_inv_plus_bi_dx/
qed-.

(*** lt_plus_to_lt_r *)
lemma nlt_inv_plus_bi_sx (m) (n1) (n2): m + n1 < m + n2 → n1 < n2.
#m #n1 #n2 #H0
lapply (nlt_inv_le … H0) -H0 #H0
/3 width=2 by nlt_le, nle_inv_plus_bi_sx/
qed-.
