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

(* NON-NEGATIVE INTEGERS ****************************************************)

definition nsucc: nat → nat ≝ λm. match m with
[ nzero  ⇒ ninj (𝟏)
| ninj p ⇒ ninj (↑p)
].

interpretation
  "successor (non-negative integers"
  'UpArrow m = (nsucc m).

(* Basic rewrites ***********************************************************)

lemma nsucc_zero: ninj (𝟏) = ↑𝟎.
// qed.

lemma nsucc_inj (p): ninj (↑p) = ↑(ninj p).
// qed.

(* Basic eliminations *******************************************************)

(*** nat_ind *)
lemma nat_ind (Q:predicate …):
      Q (𝟎) → (∀n. Q n → Q (↑n)) → ∀n. Q n.
#Q #IH1 #IH2 * //
#p elim p -p /2 width=1 by/
qed-.

(*** nat_elim2 *)
lemma nat_ind_2 (Q:relation2 …):
      (∀n. Q (𝟎) n) →
      (∀m. Q (↑m) (𝟎)) →
      (∀m,n. Q m n → Q (↑m) (↑n)) →
      ∀m,n. Q m n.
#Q #IH1 #IH2 #IH3 #m elim m -m [ // ]
#m #IH #n elim n -n /2 width=1 by/
qed-.

(* Basic inversions *********************************************************)

(*** injective_S *)
lemma eq_inv_nsucc_bi: injective … nsucc.
* [| #p1 ] * [2,4: #p2 ]
[1,4: <nsucc_zero <nsucc_inj #H destruct
| <nsucc_inj <nsucc_inj #H destruct //
| //
]
qed-.

lemma eq_inv_nsucc_zero (m): ↑m = 𝟎 → ⊥.
* [ <nsucc_zero | #p <nsucc_inj ] #H destruct
qed-.

lemma eq_inv_nzero_succ (m): 𝟎 = ↑m → ⊥.
* [ <nsucc_zero | #p <nsucc_inj ] #H destruct
qed-.
