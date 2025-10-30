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

include "ground/arith/pnat_plus.ma".
include "ground/arith/pnat_le.ma".

(* ORDER FOR POSITIVE INTEGERS **********************************************)

(* Constructions with pplus *************************************************)

lemma ple_plus_bi_dx (p) (q1) (q2): q1 ≤ q2 → q1 + p ≤ q2 + p.
#p #q1 #q2 #H elim H -q2 /2 width=3 by ple_trans/
qed.

lemma ple_plus_bi_sx (p) (q1) (q2): q1 ≤ q2 → p + q1 ≤ p + q2.
#p #q1 #q2 #H <pplus_comm <pplus_comm in ⊢ (??%);
/2 width=1 by ple_plus_bi_dx/
qed.
