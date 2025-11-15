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

include "ground/arith/nat_le.ma".
include "ground/arith//nat_ppred_psucc.ma".

(* ORDER FOR NON-NEGATIVE INTEGERS ******************************************)

(* Constructions with pnpred ************************************************)

lemma nle_ppred_bi (p1) (p2):
      p1 ≤ p2 → ↓p1 ≤ ↓p2.
//
qed.

(* Inversions with pnpred ***************************************************)

lemma nle_inv_ppred_bi (p1) (p2):
      ↓p1 ≤ ↓p2 → p1 ≤ p2.
//
qed-.
