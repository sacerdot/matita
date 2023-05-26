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

definition int_increasing_2: predicate (ℤ→ℤ) ≝
           λf. ∀z1,z2. z1 < z2 → f z1 < f z2.

definition int_increasing_1: predicate (ℤ→ℤ) ≝
           λf. ∀z. f z < f (↑z).

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

(* Constructions with int_increasing ****************************************)

lemma int_increasing_2_1 (f):
      int_increasing_2 f → int_increasing_1 f.
/2 width=1 by/
qed.

lemma int_increasing_1_2 (f):
      int_increasing_1 f → int_increasing_2 f.
#f #Hf #z1 #z2 #Hz elim Hz -z2
/2 width=3 by zlt_trans/
qed-.

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
