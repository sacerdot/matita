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

include "ground/arith/nat_le.ma".

(* STRICT ORDER FOR NON-NEGATIVE INTEGERS ***********************************)

(*** lt *)
definition nlt: relation2 nat nat ≝
           λm,n. ↑m ≤ n.

interpretation
  "less (non-negative integers)"
  'lt m n = (nlt m n).

(* Basic constructions ******************************************************)

lemma nlt_i (m) (n): ↑m ≤ n → m < n.
// qed.

lemma nlt_refl_succ (n): n < ↑n.
// qed.

(*** lt_O_S *)
lemma nlt_zero_succ (m): 𝟎 < ↑m.
/2 width=1 by nle_succ_bi/ qed.

lemma nlt_succ_bi (m) (n): m < n → ↑m < ↑n.
/2 width=1 by nle_succ_bi/ qed.

(*** le_to_or_lt_eq *)
lemma nle_lt_eq_e (m) (n): m ≤ n → ∨∨ m < n | m = n.
#m #n * -n /3 width=1 by nle_succ_bi, or_introl/
qed-.

(*** eq_or_gt *)
lemma eq_gt_e (n): ∨∨ 𝟎 = n | 𝟎 < n.
#n elim (nle_lt_eq_e (𝟎) n ?)
/2 width=1 by or_introl, or_intror/
qed-.

(*** lt_or_ge *)
lemma nlt_ge_e (m) (n): ∨∨ m < n | n ≤ m.
#m #n elim (nle_ge_e m n) /2 width=1 by or_intror/
#H elim (nle_lt_eq_e … H) -H /2 width=1 by nle_refl, or_introl, or_intror/
qed-.

(*** not_le_to_lt *)
lemma le_false_nlt (m) (n): (n ≤ m → ⊥) → m < n.
#m #n elim (nlt_ge_e m n) [ // ]
#H #Hn elim Hn -Hn // 
qed.

(*** lt_to_le_to_lt *)
lemma nlt_le_trans (o) (m) (n): m < o → o ≤ n → m < n.
/2 width=3 by nle_trans/ qed-.

lemma le_nlt_trans (o) (m) (n): m ≤ o → o < n → m < n.
/3 width=3 by nle_succ_bi, nle_trans/ qed-.

(* Basic inversions *********************************************************)

(*** lt_to_not_le *)
lemma nlt_ge_false (m) (n): m < n → n ≤ m → ⊥.
/3 width=4 by nle_inv_succ_sn_refl, nlt_le_trans/ qed-.

(*** lt_to_not_eq *)
lemma nlt_inv_refl (m): m < m → ⊥.
/2 width=4 by nlt_ge_false/ qed-.

lemma nlt_inv_zero_dx (m): m < 𝟎 → ⊥.
/2 width=4 by nlt_ge_false/ qed-.

(* Basic destructions *******************************************************)

(*** lt_to_le *)
lemma nlt_des_le (m) (n): m < n → m ≤ n.
/2 width=3 by nle_trans/ qed-.

(*** ltn_to_ltO *)
lemma nlt_des_lt_O_sn (m) (n): m < n → 𝟎 < n.
/3 width=3 by le_nlt_trans/ qed-.

(* Main constructions *******************************************************)

(*** transitive_lt *)
theorem nlt_trans: Transitive … nlt.
/3 width=3 by nlt_des_le, nlt_le_trans/ qed-.

(* Advanced eliminations ****************************************************)

lemma nat_ind_lt_le (Q:predicate …):
      (∀n. (∀m. m < n → Q m) → Q n) → ∀n,m. m ≤ n → Q m.
#Q #H1 #n @(nat_ind … n) -n
[ #m #H <(nle_inv_zero_dx … H) -m
  @H1 -H1 #o #H elim (nlt_inv_zero_dx … H)
| /5 width=3 by nlt_le_trans, nle_inv_succ_bi/
]
qed-.

(*** nat_elim1 *)
lemma nat_ind_lt (Q:predicate …):
      (∀n. (∀m. m < n → Q m) → Q n) → ∀n. Q n.
/4 width=2 by nat_ind_lt_le/ qed-.
