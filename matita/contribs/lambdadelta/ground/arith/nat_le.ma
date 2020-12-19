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

include "ground/insert_eq/insert_eq_0.ma".
include "ground/arith/nat_succ.ma".

(* NON-NEGATIVE INTEGERS ****************************************************)

(*** le *)
(*** le_ind *)
inductive nle (m:nat): predicate nat ≝
| nle_refl   : nle m m
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
#m @(nat_ind … m) -m /2 width=1 by nle_succ_dx/
qed.

(*** le_S_S *)
lemma nle_succ_bi (m) (n): m ≤ n → ↑m ≤ ↑n.
#m #n #H elim H -n /2 width=1 by nle_refl, nle_succ_dx/
qed.

(*** le_or_ge *)
lemma nle_ge_e (m) (n): ∨∨ m ≤ n | n ≤ m.
#m @(nat_ind … m) -m [ /2 width=1 by or_introl/ ]
#m #IH #n @(nat_ind … n) -n [ /2 width=1 by or_intror/ ]
#n #_ elim (IH n) -IH /3 width=2 by nle_succ_bi, or_introl, or_intror/
qed-.

(* Basic inversions *********************************************************)

lemma nle_inv_succ_sn (m) (n): ↑m ≤ n → m ≤ n.
#m #n #H elim H -n /2 width=1 by nle_succ_dx/
qed-.

(*** le_S_S_to_le *)
lemma nle_inv_succ_bi (m) (n): ↑m ≤ ↑n → m ≤ n.
#m #n @(insert_eq_0 … (↑n))
#y * -y
[ #H <(eq_inv_nsucc_bi … H) -m //
| #y #Hy #H >(eq_inv_nsucc_bi … H) -n /2 width=1 by nle_inv_succ_sn/
]
qed-.

(*** le_n_O_to_eq *)
lemma nle_inv_zero_dx (m): m ≤ 𝟎 → 𝟎 = m.
#m @(insert_eq_0 … (𝟎))
#y * -y
[ #H destruct //
| #y #_ #H elim (eq_inv_nzero_succ … H)
]
qed-.

lemma nle_inv_succ_sn_refl (m): ↑m ≤ m → ⊥.
#m @(nat_ind … m) -m [| #m #IH ] #H
[ /3 width=2 by nle_inv_zero_dx, eq_inv_nzero_succ/
| /3 width=1 by nle_inv_succ_bi/
]
qed-.

(* Order properties *********************************************************)

(*** le_to_le_to_eq *)
theorem nle_antisym (m) (n): m ≤ n → n ≤ m → m = n.
#m #n #H elim H -n //
#n #_ #IH #Hn
lapply (nle_inv_succ_sn … Hn) #H
lapply (IH H) -IH -H #H destruct
elim (nle_inv_succ_sn_refl … Hn)
qed-.

(*** transitive_le *)
theorem nle_trans: Transitive … nle.
#m #n #H elim H -n /3 width=1 by nle_inv_succ_sn/
qed-.

(* Advanced constructions ***************************************************)

(*** decidable_le *)
lemma nle_dec (m) (n): Decidable … (m ≤ n).
#m #n elim (nle_ge_e m n) [ /2 width=1 by or_introl/ ]
#Hnm elim (eq_nat_dec m n) [ #H destruct /2 width=1 by nle_refl, or_introl/ ]
/4 width=1 by nle_antisym, or_intror/
qed-.
