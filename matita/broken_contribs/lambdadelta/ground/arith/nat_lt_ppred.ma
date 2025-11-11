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

include "ground/arith/nat_ppred_psucc.ma".
include "ground/arith/nat_lt.ma".

(* STRICT ORDER FOR NON-NEGATIVE INTEGERS ***********************************)

(* Constructions with pnpred ************************************************)

lemma nlt_ppred_bi (p) (q):
      p < q → ↓p < ↓q.
//
qed.

lemma nlt_pos_ppred (p):
      ↓p < (⁤p).
//
qed.

(* Inversions with pnpred ***************************************************)

lemma nlt_inv_ppred_bi (p) (q):
      ↓p < ↓q → p < q.
//
qed-.
