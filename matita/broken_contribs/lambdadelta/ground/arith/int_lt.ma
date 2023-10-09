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

include "ground/xoa/or_3.ma".
include "ground/arith/int_le.ma".

(* STRICT ORDER FOR INTEGERS ************************************************)

interpretation
  "less (integers)"
  'lt z1 z2 = (zle (zsucc z1) z2).

(* Basic constructions ******************************************************)

lemma zlt_succ_bi (z1) (z2):
      z1 < z2 → ↑z1 < ↑z2.
/2 width=1 by zle_succ_bi/
qed.

(* Main constructions *******************************************************)

theorem zlt_trans:
        Transitive … (λz1,z2. z1 < z2).
/3 width=3 by zlt_succ_bi, zle_trans/
qed.

(* Inversions with zle ******************************************************)

lemma zle_split_lt_eq (z1) (z2):
      z1 ≤ z2 → ∨∨ z1 < z2 | z1 = z2.
#z1 #z2 * -z2
/3 width=1 by zle_succ_bi, or_introl/
qed-.

(* Destructions with zle ****************************************************)

lemma zlt_le_trans (z) (z1) (z2):
      z1 < z → z ≤ z2 → z1 < z2.
/2 width=3 by zle_trans/
qed-.

lemma zle_lt_trans (z) (z1) (z2):
      z1 ≤ z → z < z2 → z1 < z2.
/3 width=3 by zle_succ_bi, zle_trans/
qed-.
