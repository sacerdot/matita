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

include "basic_2/static/ffdeq.ma".
include "basic_2/rt_computation/csx_lfdeq.ma".

(* STRONGLY NORMALIZING TERMS FOR UNBOUND PARALLEL RT-TRANSITION ************)

(* Properties with degree-based equivalence for closures ********************)

lemma csx_ffdeq_conf: ∀h,o,G1,L1,T1. ⦃G1, L1⦄ ⊢ ⬈*[h, o] 𝐒⦃T1⦄ →
                      ∀G2,L2,T2. ⦃G1, L1, T1⦄ ≛[h, o] ⦃G2, L2, T2⦄ → ⦃G2, L2⦄ ⊢ ⬈*[h, o] 𝐒⦃T2⦄.
#h #o #G1 #L1 #T1 #HT1 #G2 #L2 #T2 * -G2 -L2 -T2
/3 width=3 by csx_lfdeq_conf, csx_tdeq_trans/
qed-.
