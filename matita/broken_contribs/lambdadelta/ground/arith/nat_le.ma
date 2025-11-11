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

include "ground/arith/pnat_le.ma".
include "ground/arith/nat_succ.ma".

(* ORDER FOR NON-NEGATIVE INTEGERS ******************************************)

(* Note: includes: ple_npsucc_bi *)
(*** le *)
definition nle: relation2 (ℕ) (ℕ) ≝
           λn1,n2. ↑n1 ≤ ↑n2.

interpretation
  "less equal (non-negative integers)"
  'leq m n = (nle m n).

(* Basic constructions ******************************************************)

lemma nle_unfold (n1:ℕ) (n2:ℕ):
      (↑n1 ≤ ↑n2) = (n1 ≤ n2).
// qed.

(*** le_n *)
lemma nle_refl: reflexive … nle.
// qed.

(*** le_S *)
lemma nle_succ_dx (m) (n):
      m ≤ n → m ≤ (⁤↑n).
/2 width=1 by ple_succ_dx/
qed.

(*** le_n_Sn *)
lemma nle_succ_dx_refl (m): m ≤ (⁤↑m).
/2 width=1 by nle_refl, nle_succ_dx/
qed.

(*** le_O_n *)
lemma nle_zero_sx (m): 𝟎 ≤ m.
//
qed.

(*** le_S_S *)
lemma nle_succ_bi (m) (n): m ≤ n → (⁤↑m) ≤ (⁤↑n).
/2 width=1 by ple_succ_bi/
qed.

(*** le_or_ge *)
lemma nat_split_le_ge (m) (n): ∨∨ m ≤ n | n ≤ m.
/2 width=1 by pnat_split_le_ge/
qed-.

lemma nle_pos_bi (p1) (p2):
      p1 ≤ p2 → (⁤p1) ≤ (⁤p2).
#p1 #p2 #Hp elim Hp -p2 //
#p2 #IH #Hp
/2 width=1 by nle_succ_dx/
qed.

(* Basic destructions *******************************************************)

lemma nle_des_succ_sx (m) (n): (⁤↑m) ≤ n → m ≤ n.
/2 width=1 by ple_des_succ_sx/
qed-.

(* Basic inversions *********************************************************)

lemma nle_inv_succ_dx (m) (n):
      m ≤ (⁤↑n) → ∨∨ m = (⁤↑n) | m ≤ n.
#m #n #H0
elim (ple_inv_succ_dx … H0)
[ >npsucc_pos #H0
  <(eq_inv_npsucc_bi … H0) -H0
  /2 width=1 by or_introl/
| /2 width=1 by or_intror/
]
qed-.

(*** le_S_S_to_le *)
lemma nle_inv_succ_bi (m) (n): (⁤↑m) ≤ (⁤↑n) → m ≤ n.
/2 width=1 by ple_inv_succ_bi/
qed-.

(*** le_n_O_to_eq *)
lemma nle_inv_zero_dx (m): m ≤ 𝟎 → 𝟎 = m.
/3 width=1 by eq_inv_npsucc_bi, ple_inv_unit_dx/
qed-.

(* Advanced inversions ******************************************************)

(*** le_plus_xSy_O_false *)
lemma nle_inv_succ_zero (m): (⁤↑m) ≤ 𝟎 → ⊥.
/3 width=2 by nle_inv_zero_dx, eq_inv_zero_npos/
qed-.

lemma nle_inv_succ_sx_refl (m): (⁤↑m) ≤ m → ⊥.
/2 width=2 by ple_inv_succ_sx_refl/
qed-.

(*** le_to_le_to_eq *)
theorem nle_antisym (m) (n): m ≤ n → n ≤ m → m = n.
/3 width=1 by eq_inv_npsucc_bi, ple_antisym/
qed-.

lemma nle_inv_pos_bi (p1) (p2):
      (⁤p1) ≤ (⁤p2) → p1 ≤ p2.
/2 width=1 by ple_inv_succ_bi/
qed-.

(* Advanced eliminations ****************************************************)

lemma nle_ind (m) (Q:predicate nat):
      Q m → (∀n. m ≤ n → Q n → Q (⁤↑n)) →
      ∀n. m ≤ n → Q n.
#m #Q #IH1 #IH2 #n @(nat_ind_succ … n) -n
[ #H0 >(nle_inv_zero_dx … H0) -H0 //
| #n #IH #H0 elim (nle_inv_succ_dx … H0) -H0 #H0 destruct
  /3 width=1 by/
]
qed-.

(*** le_elim *)
lemma nle_ind_alt (Q: relation2 nat nat):
      (∀n. Q (𝟎) (n)) →
      (∀m,n. m ≤ n → Q m n → Q (⁤↑m) (⁤↑n)) →
      ∀m,n. m ≤ n → Q m n.
#Q #IH1 #IH2 #m #n @(nat_ind_2_succ … m n) -m -n //
[ #m #_ #H elim (nle_inv_succ_zero … H)
| /4 width=1 by nle_inv_succ_bi/
]
qed-.

(* Advanced constructions ***************************************************)

(*** transitive_le *)
theorem nle_trans: Transitive … nle.
/2 width=3 by ple_trans/
qed-.

(*** decidable_le le_dec *)
lemma nle_dec (m) (n): Decidable … (m ≤ n).
#m #n elim (nat_split_le_ge m n) [ /2 width=1 by or_introl/ ]
#Hnm elim (eq_nat_dec m n) [ #H destruct /2 width=1 by nle_refl, or_introl/ ]
/4 width=1 by nle_antisym, or_intror/
qed-.
