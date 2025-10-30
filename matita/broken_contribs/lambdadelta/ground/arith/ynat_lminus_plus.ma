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

include "ground/arith/nat_minus_plus.ma".
include "ground/arith/ynat_plus.ma".
include "ground/arith/ynat_lminus_succ.ma".

(* LEFT SUBTRACTION FOR NON-NEGATIVE INTEGERS WITH INFINITY *****************)

(* Constructions with yplus *************************************************)

(*** yplus_minus *)
lemma ylminus_plus_sx_refl_sx (x) (n):
      x = x + yinj_nat n - n.
#x @(ynat_split_nat_inf … x) -x //
#n <yplus_inf_sx //
qed.

(*** yminus_plus2 *)
lemma yminus_plus_dx (x:ynat) (n) (o):
      x - n - o = x - (n + o).
#x @(ynat_split_nat_inf … x) -x //
qed.
