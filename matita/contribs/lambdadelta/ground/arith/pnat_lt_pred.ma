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

include "ground/arith/pnat_le_pred.ma".
include "ground/arith/pnat_lt.ma".

(* STRICT ORDER FOR POSITIVE INTEGERS ***************************************)

(* Destructions with ppred **************************************************)

lemma plt_des_gen (p) (q): p < q → q = ↑↓q.
#p #q elim q -q //
#H elim (plt_inv_unit_dx … H)
qed-.

(* Inversions with ppred ****************************************************)

lemma plt_inv_gen (p) (q): p < q → ∧∧ p ≤ ↓q & q = ↑↓q.
/2 width=1 by ple_inv_succ_sn/ qed-.

lemma plt_inv_succ_sn (p) (q): ↑p < q → ∧∧ p < ↓q & q = ↑↓q.
/2 width=1 by ple_inv_succ_sn/ qed-.

lemma plt_inv_pred_dx (p) (q): p < ↓q → ↑p < q.
#p #q #H >(plt_des_gen (𝟏) q)
[ /2 width=1 by plt_succ_bi/
| /3 width=3 by ple_plt_trans, plt_ple_trans/
]
qed-.

lemma plt_inv_pred_bi (p) (q):
      ↓p < ↓q → p < q.
/3 width=3 by plt_inv_pred_dx, ple_plt_trans/
qed-.

(* Constructions with ppred *************************************************)

lemma plt_unit_sn (q): q = ↑↓q → 𝟏 < q.
// qed.

lemma plt_pred_bi (p) (q): 𝟏 < p → p < q → ↓p < ↓q.
#p #q #Hp #Hpq
@ple_inv_succ_bi
<(plt_des_gen … Hp) -Hp
<(plt_des_gen … Hpq) //
qed.
