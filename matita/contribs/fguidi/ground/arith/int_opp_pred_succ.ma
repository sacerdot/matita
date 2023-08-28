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

include "ground/arith/int_opp.ma".
include "ground/arith/int_pred.ma".
include "ground/arith/int_succ.ma".

(* OPPOSITE FOR INTEGERS ****************************************************)

(* Constructions with zpred and zsucc ***************************************)

lemma zopp_pred (z): ↑-z = -↓z.
@int_ind_psucc //
qed.

lemma zopp_succ (z): ↓-z = -↑z.
@int_ind_psucc //
qed.
