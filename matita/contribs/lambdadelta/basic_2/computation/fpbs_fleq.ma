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

include "basic_2/multiple/fleq.ma".
include "basic_2/computation/fpbs.ma".

(* "BIG TREE" PARALLEL COMPUTATION FOR CLOSURES *****************************)

(* Properties on lazy equivalence on closures *******************************)

lemma fleq_fpbs: ∀h,g,G1,G2,L1,L2,T1,T2.
                 ⦃G1, L1, T1⦄ ≡[0] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 * /2 width=1 by lleq_fpbs/
qed.
