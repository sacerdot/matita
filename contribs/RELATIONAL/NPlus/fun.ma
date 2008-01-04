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

set "baseuri" "cic:/matita/RELATIONAL/NPlus/fun".

include "NPlus/inv.ma".

(* Functional properties ****************************************************)

theorem nplus_total: \forall p,q. \exists r. p + q == r.
 intros 2. elim q; clear q;
 [ autobatch | decompose. autobatch ].
qed.

theorem nplus_mono: \forall p,q,r1. (p + q == r1) \to 
                    \forall r2. (p + q == r2) \to r1 = r2.
 intros 4. elim H; clear H q r1;
 [ lapply linear nplus_inv_zero_2 to H1
 | lapply linear nplus_inv_succ_2 to H3. decompose
 ]; destruct; autobatch.
qed.

theorem nplus_inj_1: \forall p1, q, r. (p1 + q == r) \to
                     \forall p2. (p2 + q == r) \to p2 = p1.
 intros 4. elim H; clear H q r;
 [ lapply linear nplus_inv_zero_2 to H1
 | lapply linear nplus_inv_succ_2_3 to H3
 ]; autobatch.
qed.
