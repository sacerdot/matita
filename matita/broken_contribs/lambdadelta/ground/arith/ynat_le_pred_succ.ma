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

include "ground/arith/ynat_succ.ma".
include "ground/arith/ynat_le_pred.ma".

(* ORDER FOR NON-NEGATIVE INTEGERS WITH INFINITY ****************************)

(* Constructions with ypred and ysucc ***************************************)

(*** yle_refl_SP_dx *)
lemma yle_succ_pred_dx_refl (x): x ≤ ↑↓x.
#x @(ynat_split_nat_inf … x) -x
/2 width=1 by yle_inj/
qed.

(*** yle_inv_succ2 *)
lemma yle_pred_sn (x) (y): x ≤ ↑y → ↓x ≤ y.
#x #y0 @(insert_eq_1 … (↑y0))
#y * -x -y
[ #m #n0 #Hmn #H
  elim (eq_inv_ysucc_inj … H) -H #n #H1 #H2 destruct
  /3 width=1 by yle_inj, nle_pred_sn/
| #x0 #H <(eq_inv_ysucc_inf … H) -y0 //
]
qed.

(* Inversions with ypred and ysucc ******************************************)

(*** yle_succ2 *)
lemma yle_inv_pred_sn (x) (y): ↓x ≤ y → x ≤ ↑y.
#x0 #y @(insert_eq_1 … (↓x0))
#x * -x -y // #m0 #n #Hmn #H
elim (eq_inv_ypred_inj … H) -H #m #H1 #H2 destruct
/3 width=1 by yle_inj, nle_inv_pred_sn/
qed-.

(*** yle_inv_succ1 *)
lemma yle_inv_succ_sn (x) (y):
      ↑x ≤ y → ∧∧ x ≤ ↓y & y = ↑↓y.
#x0 #y @(insert_eq_1 … (↑x0))
#x * -x -y
[ #m0 #n #Hmn #H
  elim (eq_inv_ysucc_inj … H) -H #m #H1 #H2 destruct
  elim (nle_inv_succ_sn … Hmn) -Hmn #Hmn #Hn
  /3 width=1 by yle_inj, conj/
| /2 width=1 by yle_inf, conj/
]
qed-.
