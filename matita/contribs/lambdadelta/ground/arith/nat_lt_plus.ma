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

(* NON-NEGATIVE INTEGERS ****************************************************)

(* Basic constructions with plus ********************************************)

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

(*** lt_plus_Sn_r *) (**)
lemma lt_plus_Sn_r: ∀a,x,n. a < a + x + ↑n.
/2 width=1/ qed-.

(* Basic inversions with plus ***********************************************)

(*** lt_plus_to_lt_l *)
lemma nlt_inv_plus_bi_dx (m) (n1) (n2): n1 + m < n2 + m → n1 < n2.
/2 width=2 by nle_inv_plus_bi_dx/ qed-.

(*** lt_plus_to_lt_r *)
lemma nlt_inv_plus_bi_sn (m) (n1) (n2): m + n1 < m + n2 → n1 < n2.
/2 width=2 by nle_inv_plus_bi_sn/ qed-.
