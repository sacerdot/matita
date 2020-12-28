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

include "ground/arith/nat_pred_succ.ma".
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
