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

include "basic_2/rt_computation/fpbs_lfpxs.ma".
include "basic_2/rt_computation/fpbg.ma".

(* PROPER PARALLEL RST-COMPUTATION FOR CLOSURES *****************************)

(* Properties with uncounted parallel rt-computation on referred entries ****)

(* Basic_2A1: uses: lpxs_fpbg *)
lemma lfpxs_lfdneq_fpbg: ∀h,o,G,L1,L2,T. ⦃G, L1⦄ ⊢ ⬈*[h, T] L2 →
                         (L1 ≛[h, o, T] L2 → ⊥) → ⦃G, L1, T⦄ >[h, o] ⦃G, L2, T⦄.
#h #o #G #L1 #L2 #T #H #H0
elim (lfpxs_lfdneq_inv_step_sn … H … H0) -H -H0
/4 width=7 by fpb_lfpx, lfpxs_ffdeq_fpbs, ffdeq_intro_sn, ex2_3_intro/
qed.
