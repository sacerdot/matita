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

include "ground/arith/nat.ma".

(* SUCCESSOR FOR NON-NEGATIVE INTEGERS **************************************)

definition npsucc (m): pnat ≝
match m with
[ nzero  ⇒ 𝟏
| ninj p ⇒ ↑p
].

interpretation
  "positive successor (non-negative integers)"
  'UpArrow m = (npsucc m).

definition nsucc (m): nat ≝
           ninj (↑m).

interpretation
  "successor (non-negative integers)"
  'UpArrow m = (nsucc m).

(* Basic constructions ******************************************************)

lemma npsucc_zero: (𝟏) = ↑𝟎.
// qed.

lemma npsucc_inj (p): (↑p) = ↑(ninj p).
// qed.

lemma nsucc_unfold (n): ninj (↑n) = ↑n.
// qed-.

lemma nsucc_zero: ninj (𝟏) = ↑𝟎.
// qed.

lemma nsucc_inj (p): ninj (↑p) = ↑(ninj p).
// qed.

lemma npsucc_succ (n): psucc (npsucc n) = npsucc (nsucc n).
// qed.

(* Basic eliminations *******************************************************)

(*** nat_ind *)
lemma nat_ind_succ (Q:predicate …):
      Q (𝟎) → (∀n. Q n → Q (↑n)) → ∀n. Q n.
#Q #IH1 #IH2 * //
#p elim p -p /2 width=1 by/
qed-.

(*** nat_elim2 *)
lemma nat_ind_2_succ (Q:relation2 …):
      (∀n. Q (𝟎) n) →
      (∀m. Q m (𝟎) → Q (↑m) (𝟎)) →
      (∀m,n. Q m n → Q (↑m) (↑n)) →
      ∀m,n. Q m n.
#Q #IH1 #IH2 #IH3 #m @(nat_ind_succ … m) -m [ // ]
#m #IH #n @(nat_ind_succ … n) -n /2 width=1 by/
qed-.

(* Basic inversions *********************************************************)

lemma eq_inv_npsucc_bi: injective … npsucc.
* [| #p1 ] * [2,4: #p2 ]
[ 1,4: <npsucc_zero <npsucc_inj #H destruct
| <npsucc_inj <npsucc_inj #H destruct //
| //
]
qed-.

(*** injective_S *)
lemma eq_inv_nsucc_bi: injective … nsucc.
#n1 #n2 #H
@eq_inv_npsucc_bi @eq_inv_ninj_bi @H
qed-.

lemma eq_inv_nsucc_zero (m): ↑m = 𝟎 → ⊥.
* [ <nsucc_zero | #p <nsucc_inj ] #H destruct
qed-.

lemma eq_inv_zero_nsucc (m): 𝟎 = ↑m → ⊥.
* [ <nsucc_zero | #p <nsucc_inj ] #H destruct
qed-.

(*** succ_inv_refl_sn *)
lemma nsucc_inv_refl (n): n = ↑n → ⊥.
#n @(nat_ind_succ … n) -n
[ /2 width=2 by eq_inv_zero_nsucc/
| #n #IH #H /3 width=1 by eq_inv_nsucc_bi/
]
qed-.
