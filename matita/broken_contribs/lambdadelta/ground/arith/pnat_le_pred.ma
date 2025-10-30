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

include "ground/arith/pnat_pred.ma".
include "ground/arith/pnat_le.ma".

(* ORDER FOR POSITIVE INTEGERS **********************************************)

(* Destructions with ppred **************************************************)

lemma ple_inv_pred_sx (p) (q): ⫰p ≤ q → p ≤ ↑q.
#p #q elim p -p
/2 width=1 by ple_succ_bi/
qed-.

(* Constructions with ppred *************************************************)

lemma ple_succ_pred_dx_refl (p): p ≤ ↑⫰p.
#p @ple_inv_pred_sx // qed.

lemma ple_pred_sx_refl (p): ⫰p ≤ p.
#p elim p -p //
qed.

lemma ple_pred_bi (p) (q): p ≤ q → ⫰p ≤ ⫰q.
#p #q #H elim H -q //
/2 width=3 by ple_trans/
qed.

lemma ple_pred_sx (p) (q): p ≤ ↑q → ⫰p ≤ q.
#p #q elim p -p //
/2 width=1 by ple_pred_bi/
qed-.

(* Inversions with ppred ****************************************************)

lemma ple_inv_succ_sx (p) (q):
      ↑p ≤ q → ∧∧ p ≤ ⫰q & q = ↑⫰q.
#p #q * -q
[ /2 width=3 by ple_refl, conj/
| #q #Hq /3 width=1 by ple_des_succ_sx, conj/
]
qed-.
