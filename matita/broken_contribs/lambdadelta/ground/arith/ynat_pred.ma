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

include "ground/arith/nat_pred.ma".
include "ground/arith/ynat_nat.ma".

(* PREDECESSOR FOR NON-NEGATIVE INTEGERS WITH INFINITY **********************)

definition ypred_aux (n): ynat ≝
           yinj_nat (↓n).

(*** ypred *)
definition ypred: ynat → ynat ≝
           ynat_bind_nat ypred_aux (∞).

interpretation
  "successor (non-negative integers with infinity)"
  'DownArrow x = (ypred x).

(* Constructions ************************************************************)

(*** ypred_O *)
lemma ypred_inj (n): yinj_nat (↓n) = ↓(yinj_nat n).
@(ynat_bind_nat_inj ypred_aux)
qed.

(*** ypred_Y *)
lemma ypred_inf: ∞ = ↓∞.
// qed.

(* Inversions ***************************************************************)

lemma eq_inv_ypred_inj (x) (n):
      ↓x = yinj_nat n →
      ∃∃m. x = yinj_nat m & n = ↓m.
#x #n @(ynat_split_nat_inf … x) -x
[ #m <ypred_inj #H <(eq_inv_yinj_nat_bi … H) -n
  /2 width=3 by ex2_intro/
| #H elim (eq_inv_inf_yinj_nat … H)
]
qed-.

(*** ypred_inv_refl *)
lemma ypred_inv_refl (x): x = ↓x → ∨∨ 𝟎 = x | ∞ = x.
#x @(ynat_split_nat_inf … x) -x //
#n <ypred_inj #H
lapply (eq_inv_yinj_nat_bi … H) -H #H
lapply (npred_inv_refl … H) -H #H
/2 width=1 by or_introl/
qed-.
