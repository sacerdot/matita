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
include "ground/arith/nat_lt.ma".

(* STRICT ORDER FOR NON-NEGATIVE INTEGERS ***********************************)

(* Constructions with nle ***************************************************)

lemma nlt_le (m) (n): (⁤↑m) ≤ n → m < n.
//
qed.

lemma nlt_succ_dx (m) (n): m ≤ n → m < (⁤↑n).
/2 width=1 by nle_succ_bi/
qed.

(*** le_to_or_lt_eq *)
lemma nle_split_lt_eq (m) (n): m ≤ n → ∨∨ m < n | m = n.
#m #n #H0 elim (ple_split_lt_eq … H0) -H0
[ /2 width=1 by or_introl/
| /3 width=1 by eq_inv_npsucc_bi, or_intror/
]
qed-.

(*** lt_or_ge *)
lemma nat_split_lt_ge (m) (n): ∨∨ m < n | n ≤ m.
#m #n elim (nat_split_le_ge m n) /2 width=1 by or_intror/
#H elim (nle_split_lt_eq … H) -H /2 width=1 by nle_refl, or_introl, or_intror/
qed-.

(*** not_le_to_lt *)
lemma le_false_nlt (m) (n): (n ≤ m → ⊥) → m < n.
#m #n elim (nat_split_lt_ge m n) [ // ]
#H #Hn elim Hn -Hn //
qed.

(*** lt_to_le_to_lt *)
lemma nlt_nle_trans (o) (m) (n): m < o → o ≤ n → m < n.
/2 width=3 by plt_ple_trans/
qed-.

(*** le_to_lt_to_lt *)
lemma nle_nlt_trans (o) (m) (n): m ≤ o → o < n → m < n.
/2 width=3 by ple_plt_trans/
qed-.

(* Inversions with nle ******************************************************)

lemma nlt_inv_le (m) (n): m < n → (⁤↑m) ≤ n.
#m #n
<nlt_unfold //
qed-.

lemma nlt_inv_succ_dx_le (m) (n): m < (⁤↑n) → m ≤ n.
/2 width=1 by plt_inv_succ_dx/
qed-.

(*** lt_to_not_le lt_le_false *)
lemma nlt_ge_false (m) (n): m < n → n ≤ m → ⊥.
/3 width=4 by nle_inv_succ_sx_refl, nlt_nle_trans/
qed-.

(* Destructions with nle ****************************************************)

(*** lt_to_le *)
lemma nlt_des_le (m) (n): m < n → m ≤ n.
/3 width=3 by nlt_inv_le, nle_trans/
qed-.

(* Eliminations with nle ****************************************************)

lemma nat_ind_lt_le (Q:predicate …):
      (∀n. (∀m. m < n → Q m) → Q n) → ∀n,m. m ≤ n → Q m.
#Q #H1 #n @(nat_ind_succ … n) -n
[ #m #H <(nle_inv_zero_dx … H) -m
  @H1 -H1 #o #H elim (nlt_inv_zero_dx … H)
| /5 width=3 by nlt_nle_trans, nle_inv_succ_bi/
]
qed-.
