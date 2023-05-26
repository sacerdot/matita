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

include "ground/notation/functions/naturals_0.ma".
include "ground/notation/functions/zero_0.ma".
include "ground/arith/pnat.ma".

(* NON-NEGATIVE INTEGERS ****************************************************)

(*** nat *)
inductive nat: Type[0] ≝
| nzero: nat
| npos : ℕ⁺ → nat
.

coercion npos.

interpretation
  "non-negative integers"
  'Naturals = (nat).

interpretation
  "zero (non-negative integers)"
  'Zero = (nzero).

(* Basic inversions *********************************************************)

(* Note: destruct *)
lemma eq_inv_npos_zero (p): npos p = 𝟎 → ⊥.
#p #H0 destruct
qed-.

(* Note: destruct *)
lemma eq_inv_zero_npos (p): 𝟎 = npos p → ⊥.
#p #H0 destruct
qed-.

(* Note: destruct *)
lemma eq_inv_npos_bi: injective … npos.
#p1 #p2 #H destruct //
qed-.

(* Basic constructions ******************************************************)

(*** eq_nat_dec *)
lemma eq_nat_dec (n1,n2:ℕ): Decidable (n1 = n2).
* [| #p1 ] * [2,4: #p2 ]
[1,4: @or_intror #H destruct
| elim (eq_pnat_dec p1 p2)
  /4 width=1 by eq_inv_npos_bi, or_intror, or_introl/
| /2 width=1 by or_introl/
]
qed-.
