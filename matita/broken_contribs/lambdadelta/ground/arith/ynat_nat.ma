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
include "ground/arith/ynat.ma".

(* NAT-INJECTION FOR NON-NEGATIVE INTEGERS WITH INFINITY ********************)

(*** yinj *)
definition yinj_nat (n): ynat ≝ match n with
[ nzero  ⇒ 𝟎
| ninj p ⇒ yinj p
].

definition ynat_bind_nat: (ℕ → ynat) → ynat → (ynat → ynat).
#f #y *
[ @f @(𝟎)
| #p @f @p
| @y
]
qed-.

(* Basic constructions ******************************************************)

lemma yinj_nat_zero: 𝟎 = yinj_nat (𝟎).
// qed.

lemma yinj_nat_inj (p): yinj p = yinj_nat (ninj p).
// qed.

lemma ynat_bind_nat_inj (f) (y) (n):
      f n = ynat_bind_nat f y (yinj_nat n).
#f #y * // qed.

lemma ynat_bind_nat_inf (f) (y):
      y = ynat_bind_nat f y (∞).
// qed.

(* Basic inversions *********************************************************)

lemma eq_inv_yinj_nat_inf (n1): yinj_nat n1 = ∞ → ⊥.
* [| #p1 ]
[ <yinj_nat_zero #H destruct
| <yinj_nat_inj #H destruct
]
qed.

lemma eq_inv_inf_yinj_nat (n2): ∞ = yinj_nat n2 → ⊥.
/2 width=2 by eq_inv_yinj_nat_inf/ qed-.

(*** yinj_inj *)
lemma eq_inv_yinj_nat_bi (n1) (n2): yinj_nat n1 = yinj_nat n2 → n1 = n2.
* [| #p1 ] * [2,4: #p2 ]
[ <yinj_nat_zero <yinj_nat_inj #H destruct
| <yinj_nat_inj <yinj_nat_inj #H destruct //
| //
| <yinj_nat_inj <yinj_nat_zero #H destruct
]
qed-.

(* Basic eliminations *******************************************************)

lemma ynat_split_nat_inf (Q:predicate …):
      (∀n. Q (yinj_nat n)) → Q (∞) → ∀y. Q y.
#Q #H1 #H2 * //
qed-.
