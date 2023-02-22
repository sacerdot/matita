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

include "ground/generated/insert_eq_1.ma".
include "ground/arith/nat_succ.ma".

(* ORDER FOR NON-NEGATIVE INTEGERS ******************************************)

(*** le *)
inductive nle (m:nat): predicate nat ≝
(*** le_n *)
| nle_refl   : nle m m
(*** le_S *)
| nle_succ_dx: ∀n. nle m n → nle m (↑n)
.

interpretation
  "less equal (non-negative integers)"
  'leq m n = (nle m n).

(* Basic constructions ******************************************************)

(*** le_n_Sn *)
lemma nle_succ_dx_refl (m): m ≤ ↑m.
/2 width=1 by nle_refl, nle_succ_dx/ qed.

(*** le_O_n *)
lemma nle_zero_sx (m): 𝟎 ≤ m.
#m @(nat_ind_succ … m) -m /2 width=1 by nle_succ_dx/
qed.

(*** le_S_S *)
lemma nle_succ_bi (m) (n): m ≤ n → ↑m ≤ ↑n.
#m #n #H elim H -n /2 width=1 by nle_refl, nle_succ_dx/
qed.

(*** le_or_ge *)
lemma nat_split_le_ge (m) (n): ∨∨ m ≤ n | n ≤ m.
#m #n @(nat_ind_2_succ … m n) -m -n
[ /2 width=1 by or_introl/
| /2 width=1 by or_intror/
| #m #n * /3 width=2 by nle_succ_bi, or_introl, or_intror/
]
qed-.

(* Basic destructions *******************************************************)

lemma nle_des_succ_sn (m) (n): ↑m ≤ n → m ≤ n.
#m #n #H elim H -n /2 width=1 by nle_succ_dx/
qed-.

(* Basic inversions *********************************************************)

(*** le_S_S_to_le *)
lemma nle_inv_succ_bi (m) (n): ↑m ≤ ↑n → m ≤ n.
#m #n @(insert_eq_1 … (↑n))
#x * -x
[ #H >(eq_inv_nsucc_bi … H) -n //
| #o #Ho #H >(eq_inv_nsucc_bi … H) -n
  /2 width=1 by nle_des_succ_sn/ 
]
qed-.

(*** le_n_O_to_eq *)
lemma nle_inv_zero_dx (m): m ≤ 𝟎 → 𝟎 = m.
#m @(insert_eq_1 … (𝟎))
#y * -y
[ #H destruct //
| #y #_ #H elim (eq_inv_zero_nsucc … H)
]
qed-.

(* Advanced inversions ******************************************************)

(*** le_plus_xSy_O_false *)
lemma nle_inv_succ_zero (m): ↑m ≤ 𝟎 → ⊥.
/3 width=2 by nle_inv_zero_dx, eq_inv_zero_nsucc/ qed-.

lemma nle_inv_succ_sn_refl (m): ↑m ≤ m → ⊥.
#m @(nat_ind_succ … m) -m [| #m #IH ] #H
[ /2 width=2 by nle_inv_succ_zero/
| /3 width=1 by nle_inv_succ_bi/
]
qed-.

(*** le_to_le_to_eq *)
theorem nle_antisym (m) (n): m ≤ n → n ≤ m → m = n.
#m #n #H elim H -n //
#n #_ #IH #Hn
lapply (nle_des_succ_sn … Hn) #H
lapply (IH H) -IH -H #H destruct
elim (nle_inv_succ_sn_refl … Hn)
qed-.

(* Advanced eliminations ****************************************************)

(*** le_elim *)
lemma nle_ind_alt (Q: relation2 nat nat):
      (∀n. Q (𝟎) (n)) →
      (∀m,n. m ≤ n → Q m n → Q (↑m) (↑n)) →
      ∀m,n. m ≤ n → Q m n.
#Q #IH1 #IH2 #m #n @(nat_ind_2_succ … m n) -m -n //
[ #m #_ #H elim (nle_inv_succ_zero … H)
| /4 width=1 by nle_inv_succ_bi/
]
qed-.

(* Advanced constructions ***************************************************)

(*** transitive_le *)
theorem nle_trans: Transitive … nle.
#m #n #H elim H -n /3 width=1 by nle_des_succ_sn/
qed-.

(*** decidable_le le_dec *)
lemma nle_dec (m) (n): Decidable … (m ≤ n).
#m #n elim (nat_split_le_ge m n) [ /2 width=1 by or_introl/ ]
#Hnm elim (eq_nat_dec m n) [ #H destruct /2 width=1 by nle_refl, or_introl/ ]
/4 width=1 by nle_antisym, or_intror/
qed-.
