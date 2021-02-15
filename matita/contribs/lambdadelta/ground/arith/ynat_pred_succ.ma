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
include "ground/arith/ynat_succ.ma".
include "ground/arith/ynat_pred.ma".

(* PREDECESSOR FOR NON-NEGATIVE INTEGERS WITH INFINITY **********************)

(* Constructions with ysucc *************************************************)

(*** ypred_succ ypred_S *)
lemma ypred_succ (x): x = ↓↑x.
#x @(ynat_split_nat_inf … x) -x //
qed.

(* Inversion with ysucc *****************************************************)

(*** ynat_cases *)
lemma ynat_split_zero_pos (x): ∨∨ 𝟎 = x | x = ↑↓x.
#x @(ynat_split_nat_inf … x) -x //
#n elim (nat_split_zero_pos n)
/2 width=1 by or_introl, or_intror/
qed-.
