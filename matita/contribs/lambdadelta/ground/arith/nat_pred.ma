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
include "ground/arith/pnat_dis.ma".
include "ground/arith/nat.ma".

(* PREDECESSOR FOR NON-NEGATIVE INTEGERS ************************************)

(*** pred *)
definition npred (m): nat ≝ match m with
[ nzero  ⇒ 𝟎
| ninj p ⇒ pdis … (𝟎) ninj p
].

interpretation
  "predecessor (non-negative integers)"
  'DownArrow m = (npred m).

(* Basic constructions ******************************************************)

(*** pred_O *)
lemma npred_zero: 𝟎 = ↓𝟎.
// qed.

lemma npred_one: 𝟎 = ↓𝟏.
// qed.

lemma npred_psucc (p): ninj p = ↓↑p.
// qed.

(* Basic inversions *********************************************************)

lemma npred_pnat_inv_refl (p): ninj p = ↓p → ⊥.
*
[ <npred_one #H destruct
| #p /3 width=2 by psucc_inv_refl, eq_inv_ninj_bi/
]
qed-.

(*** pred_inv_fix_sn *)
lemma npred_inv_refl (n): n = ↓n → 𝟎 = n.
* // #p #H elim (npred_pnat_inv_refl … H)
qed-.
