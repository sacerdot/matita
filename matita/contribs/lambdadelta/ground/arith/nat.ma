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

include "ground/notation/functions/zero_0.ma".
include "ground/arith/pnat.ma".

(* NON-NEGATIVE INTEGERS ****************************************************)

(*** nat *)
inductive nat: Type[0] ≝
| nzero: nat
| ninj : pnat → nat
.

coercion ninj.

interpretation
  "zero (non-negative integers)"
  'Zero = nzero.

(* Basic inversions *********************************************************)

(* Note: destruct *)
lemma eq_inv_ninj_bi: injective … ninj.
#p #q #H destruct //
qed-.

(* Basic constructions ******************************************************)

lemma eq_nat_dec (n1,n2:nat): Decidable (n1 = n2).
* [| #p1 ] * [2,4: #p2 ]
[1,4: @or_intror #H destruct
| elim (eq_pnat_dec p1 p2)
  /4 width=1 by eq_inv_ninj_bi, or_intror, or_introl/
| /2 width=1 by or_introl/
]
qed-.
