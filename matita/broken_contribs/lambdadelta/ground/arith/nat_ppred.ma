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

include "ground/notation/functions/downarrow_1.ma".
include "ground/arith/pnat_split.ma".
include "ground/arith/nat.ma".

(* POSITIVE PREDECESSOR FOR NON-NEGATIVE INTEGERS ***************************)

definition pnpred (p): ℕ ≝
           psplit … (𝟎) ninj p.

interpretation
  "positive predecessor (non-negative integers)"
  'DownArrow p = (pnpred p).

(* Basic constructions ******************************************************)

lemma pnpred_unit: 𝟎 = ↓𝟏.
// qed.

lemma pnpred_succ (p:ℤ⁺): p ={ℕ} ↓↑p.
// qed.

(* Basic inversions *********************************************************)

lemma eq_inv_pnpred_bi: injective … pnpred.
* [| #p1 ] * [2,4: #p2 ]
[ 1,4: <pnpred_unit <pnpred_succ #H0 destruct
| <pnpred_succ <pnpred_succ #H0 destruct //
| //
]
qed-.

lemma pnpred_inv_refl (p:ℤ⁺): p ={ℕ} ↓p → ⊥.
*
[ <pnpred_unit #H0 destruct
| #p /3 width=2 by psucc_inv_refl, eq_inv_ninj_bi/
]
qed-.
