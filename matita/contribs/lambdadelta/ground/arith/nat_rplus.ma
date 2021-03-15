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

include "ground/arith/nat_iter.ma".

(* RIGHT ADDITION FOR NON-NEGATIVE INTEGERS *********************************)

definition nrplus: pnat → nat → pnat ≝
           λp,n. psucc^n p.

interpretation
  "right plus (non-negative integers)"
  'plus p n = (nrplus p n).

(* Basic constructions ******************************************************)

lemma nrplus_zero_dx (p): p = p + 𝟎.
// qed.

lemma nrplus_unit_dx (p): ↑p = p + 𝟏.
// qed.

lemma nrplus_succ_sn (p) (n): ↑(p+n) = ↑p + n.
#p #n @(niter_appl … psucc)
qed.
