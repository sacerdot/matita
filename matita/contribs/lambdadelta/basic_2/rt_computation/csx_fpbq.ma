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

include "basic_2/rt_transition/fpbq.ma".
include "basic_2/rt_computation/csx_fqus.ma".
include "basic_2/rt_computation/csx_ffdeq.ma".
include "basic_2/rt_computation/csx_lfpx.ma".

(* STRONGLY NORMALIZING TERMS FOR UNBOUND PARALLEL RT-TRANSITION ************)

(* Properties with parallel rst-transition for closures *********************)

(* Basic_2A1: was: csx_fpb_conf *)
lemma csx_fpbq_conf: ∀h,o,G1,L1,T1. ⦃G1, L1⦄ ⊢ ⬈*[h, o] 𝐒⦃T1⦄ →
                     ∀G2,L2,T2. ⦃G1, L1, T1⦄ ≽[h, o] ⦃G2, L2, T2⦄ → ⦃G2, L2⦄ ⊢ ⬈*[h, o] 𝐒⦃T2⦄.
#h #o #G1 #L1 #T1 #HT1 #G2 #L2 #T2 *
/2 width=6 by csx_cpx_trans, csx_fquq_conf, csx_lfpx_conf, csx_ffdeq_conf/
qed-.
