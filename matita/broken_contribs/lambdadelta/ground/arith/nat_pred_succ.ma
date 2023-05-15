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

include "ground/arith/nat_ppred_succ.ma".
include "ground/arith/nat_pred.ma".

(* PREDECESSOR FOR NON-NEGATIVE INTEGERS ************************************)

(* Constructions with nsucc *************************************************)

(*** pred_Sn pred_S *)
lemma npred_succ (n): n = ⫰↑n.
//
qed.

(* Inversions with nsucc ****************************************************)

(*** nat_split *)
lemma nat_split_zero_pos (n): ∨∨ 𝟎 = n | n = ↑⫰n.
#n @(nat_ind_succ … n) -n
/2 width=1 by or_introl, or_intror/
qed-.
