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

include "ground/arith/nat_psucc.ma".
include "ground/arith/nat_ppred.ma".

(* POSITIVE PREDECESSOR FOR NON-NEGATIVE INTEGERS ***************************)

(* Constructions with npsucc ************************************************)

lemma pnpred_npsucc (n): n = ↓↑n.
* //
qed.

lemma npsucc_pnpred (p): p = ↑↓p.
* //
qed.

lemma nsucc_pnpred_swap (p): ↓↑p = (⁤↑↓p).
// (* FIXME *)
qed-.
