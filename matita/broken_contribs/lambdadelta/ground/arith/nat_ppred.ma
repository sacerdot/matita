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
           psplit … (𝟎) npos p.

interpretation
  "positive predecessor (non-negative integers)"
  'DownArrow p = (pnpred p).

(* Basic constructions ******************************************************)

lemma pnpred_unit: 𝟎 = ↓𝟏.
// qed.

lemma pnpred_succ (p): (⁤p) = ↓↑p.
// qed.

(* Basic inversions *********************************************************)

lemma eq_inv_pnpred_bi: injective … pnpred.
* [| #p1 ] * [2,4: #p2 ]
[ 1,4: <pnpred_unit <pnpred_succ #H0 destruct
| <pnpred_succ <pnpred_succ #H0 destruct //
| //
]
qed-.

lemma eq_inv_refl_pnpred (p): (⁤p) = ↓p → ⊥.
*
[ <pnpred_unit #H0 destruct
| #p /3 width=2 by eq_inv_refl_psucc, eq_inv_npos_bi/
]
qed-.
