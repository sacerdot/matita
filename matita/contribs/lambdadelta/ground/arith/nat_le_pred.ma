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

include "ground/arith/nat_pred_succ.ma".
include "ground/arith/nat_le.ma".

(* NON-NEGATIVE INTEGERS ****************************************************)

(* Basic constructions with pred ********************************************)

(*** le_pred_n *)
lemma nle_pred_sn_refl (m): ↓m ≤ m.
#m elim m -m //
qed.

(*** monotonic_pred *)
lemma nle_pred_bi (m) (n): m ≤ n → ↓m ≤ ↓n.
#m #n #H elim H -n
/2 width=3 by nle_trans/
qed.
