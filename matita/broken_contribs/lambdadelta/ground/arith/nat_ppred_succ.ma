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

include "ground/arith/nat_succ.ma".
include "ground/arith/nat_ppred_psucc.ma".

(* POSITIVE PREDECESSOR FOR NON-NEGATIVE INTEGERS ***************************)

(* Constructions with nsucc *************************************************)

lemma nsucc_pnpred_swap (p): ↓↑p = (⁤↑↓p).
//
qed-.
