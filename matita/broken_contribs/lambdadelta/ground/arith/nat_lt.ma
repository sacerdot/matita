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
include "ground/arith/nat_le.ma".

(* STRICT ORDER FOR NON-NEGATIVE INTEGERS ***********************************)

(*** lt *)
definition nlt: relation2 (ℕ) (ℕ) ≝
           λm,n. (⁤↑m) ≤ n.

interpretation
  "less (non-negative integers)"
  'lt m n = (nlt m n).

(* Basic constructions ******************************************************)

lemma nlt_i (m) (n): (⁤↑m) ≤ n → m < n.
// qed.

lemma nlt_refl_succ (n): n < (⁤↑n).
// qed.

lemma nlt_succ_dx (m) (n): m ≤ n → m < (⁤↑n).
/2 width=1 by nle_succ_bi/ qed.

(*** lt_S *)
lemma nlt_succ_dx_trans (m) (n): m < n → m < (⁤↑n).
/2 width=1 by nle_succ_dx/ qed.

(*** lt_O_S *)
lemma nlt_zero_succ (m): 𝟎 < (⁤↑m).
/2 width=1 by nle_succ_bi/ qed.

(*** lt_S_S *)
lemma nlt_succ_bi (m) (n): m < n → (⁤↑m) < (⁤↑n).
/2 width=1 by nle_succ_bi/ qed.

(*** le_to_or_lt_eq *)
lemma nle_split_lt_eq (m) (n): m ≤ n → ∨∨ m < n | m = n.
#m #n * -n /3 width=1 by nle_succ_bi, or_introl/
qed-.

(*** eq_or_gt *)
lemma nat_split_zero_gt (n): ∨∨ 𝟎 = n | 𝟎 < n.
#n elim (nle_split_lt_eq (𝟎) n ?)
/2 width=1 by or_introl, or_intror/
qed-.

(*** lt_or_ge *)
lemma nat_split_lt_ge (m) (n): ∨∨ m < n | n ≤ m.
#m #n elim (nat_split_le_ge m n) /2 width=1 by or_intror/
#H elim (nle_split_lt_eq … H) -H /2 width=1 by nle_refl, or_introl, or_intror/
qed-.

(*** lt_or_eq_or_gt *)
lemma nat_split_lt_eq_gt (m) (n): ∨∨ m < n | n = m | n < m.
#m #n elim (nat_split_lt_ge m n) /2 width=1 by or3_intro0/
#H elim (nle_split_lt_eq … H) -H /2 width=1 by or3_intro1, or3_intro2/
qed-.

(*** not_le_to_lt *)
lemma le_false_nlt (m) (n): (n ≤ m → ⊥) → m < n.
#m #n elim (nat_split_lt_ge m n) [ // ]
#H #Hn elim Hn -Hn //
qed.

(*** lt_to_le_to_lt *)
lemma nlt_nle_trans (o) (m) (n): m < o → o ≤ n → m < n.
/2 width=3 by nle_trans/ qed-.

(*** le_to_lt_to_lt *)
lemma nle_nlt_trans (o) (m) (n): m ≤ o → o < n → m < n.
/3 width=3 by nle_succ_bi, nle_trans/ qed-.

(* Basic inversions *********************************************************)

lemma nlt_inv_succ_dx (m) (n): m < (⁤↑n) → m ≤ n.
/2 width=1 by nle_inv_succ_bi/ qed-.

(*** lt_S_S_to_lt *)
lemma nlt_inv_succ_bi (m) (n): (⁤↑m) < (⁤↑n) → m < n.
/2 width=1 by nle_inv_succ_bi/ qed-.

(*** lt_to_not_le lt_le_false *)
lemma nlt_ge_false (m) (n): m < n → n ≤ m → ⊥.
/3 width=4 by nle_inv_succ_sx_refl, nlt_nle_trans/ qed-.

(*** lt_to_not_eq lt_refl_false *)
lemma nlt_inv_refl (m): m < m → ⊥.
/2 width=4 by nlt_ge_false/ qed-.

(*** lt_zero_false *)
lemma nlt_inv_zero_dx (m): m < 𝟎 → ⊥.
/2 width=4 by nlt_ge_false/ qed-.

lemma nlt_inv_zero_sx_pos (n):
      (𝟎) < n → ∃p. (⁤p) = n.
*
[ #H0 elim (nlt_inv_refl … H0)
| /2 width=2 by ex_intro/
]
qed-.

(* Basic destructions *******************************************************)

(*** lt_to_le *)
lemma nlt_des_le (m) (n): m < n → m ≤ n.
/2 width=3 by nle_trans/ qed-.

(*** ltn_to_ltO *)
lemma nlt_des_lt_zero_sx (m) (n): m < n → 𝟎 < n.
/3 width=3 by nle_nlt_trans/ qed-.

(* Main constructions *******************************************************)

(*** transitive_lt *)
theorem nlt_trans: Transitive … nlt.
/3 width=3 by nlt_des_le, nlt_nle_trans/ qed-.

(* Advanced eliminations ****************************************************)

lemma nat_ind_lt_le (Q:predicate …):
      (∀n. (∀m. m < n → Q m) → Q n) → ∀n,m. m ≤ n → Q m.
#Q #H1 #n @(nat_ind_succ … n) -n
[ #m #H <(nle_inv_zero_dx … H) -m
  @H1 -H1 #o #H elim (nlt_inv_zero_dx … H)
| /5 width=3 by nlt_nle_trans, nle_inv_succ_bi/
]
qed-.

(*** nat_elim1 *)
lemma nat_ind_lt (Q:predicate …):
      (∀n. (∀m. m < n → Q m) → Q n) → ∀n. Q n.
/4 width=2 by nat_ind_lt_le/ qed-.

(*** lt_elim *)
lemma nlt_ind_alt (Q: relation2 … (ℕ)):
      (∀n. Q (𝟎) (⁤↑n)) →
      (∀m,n. m < n → Q m n → Q (⁤↑m) (⁤↑n)) →
      ∀m,n. m < n → Q m n.
#Q #IH1 #IH2 #m #n @(nat_ind_2_succ … n m) -m -n //
[ #m #H
  elim (nlt_inv_zero_dx … H)
| /4 width=1 by nlt_inv_succ_bi/
]
qed-.

(* Advanced constructions (decidability) ************************************)

(*** dec_lt *)
lemma dec_nlt (R:predicate …):
      (∀n. Decidable … (R n)) →
      ∀n. Decidable … (∃∃m. m < n & R m).
#R #HR #n @(nat_ind_succ … n) -n [| #n * ]
[ @or_intror * /2 width=2 by nlt_inv_zero_dx/
| * /4 width=3 by nlt_succ_dx_trans, ex2_intro, or_introl/
| #H0 elim (HR n) -HR
  [ /3 width=3 by or_introl, ex2_intro/
  | #Hn @or_intror * #m #Hmn #Hm
    elim (nle_split_lt_eq … Hmn) -Hmn #H destruct [ -Hn | -H0 ]
    [ /4 width=3 by nlt_inv_succ_bi, ex2_intro/
    | lapply (eq_inv_nsucc_bi … H) -H /2 width=1 by/
  ]
]
qed-.
