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

include "ground/arith/nat_le_pred.ma".
include "ground/arith/nat_lt.ma".

(* STRICT ORDER FOR NON-NEGATIVE INTEGERS ***********************************)

(* Constructions with npred *************************************************)

lemma nlt_zero_sn (m): m = ↑↓m → 𝟎 < m.
// qed.

(* Inversions with npred ****************************************************)

(*** S_pred *)
lemma nlt_inv_zero_sn (m): 𝟎 < m → m = ↑↓m.
#m @(nat_ind … m) -m //
#H elim (nlt_inv_refl … H)
qed-.

lemma nlt_inv_pred_dx (m) (n): m < ↓n → ↑m < n.
#m #n #H >(nlt_inv_zero_sn n)
[ /2 width=1 by nlt_succ_bi/
| /3 width=3 by le_nlt_trans, nlt_le_trans/
]
qed-.
