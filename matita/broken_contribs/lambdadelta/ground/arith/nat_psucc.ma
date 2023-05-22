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

include "ground/arith/nat_split.ma".

(* POSITIVE SUCCESSOR FOR NON-NEGATIVE INTEGERS *****************************)

definition npsucc (m): ℤ⁺ ≝
           nsplit … (𝟏) psucc m.

interpretation
  "positive successor (non-negative integers)"
  'UpArrow m = (npsucc m).

(* Basic constructions ******************************************************)

lemma npsucc_zero: (𝟏) = ↑𝟎.
// qed.

lemma npsucc_inj (p): (↑p) = ↑(npos p).
// qed.

lemma npsucc_succ (n): psucc (npsucc n) = npsucc (npsucc n).
// qed.

(* Basic inversions *********************************************************)

lemma eq_inv_npsucc_bi: injective … npsucc.
* [| #p1 ] * [2,4: #p2 ]
[ 1,4: <npsucc_zero <npsucc_inj #H destruct
| <npsucc_inj <npsucc_inj #H destruct //
| //
]
qed-.

lemma eq_inv_refl_npsucc (m:ℕ): m = ↑m → ⊥.
*
[ #H0 destruct
| #p #H0 /3 width=2 by eq_inv_npos_bi, eq_inv_refl_psucc/
]
qed-.
