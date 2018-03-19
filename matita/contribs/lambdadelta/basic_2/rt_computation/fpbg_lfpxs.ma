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

include "basic_2/computation/lpxs_ffdeq.ma".
include "basic_2/computation/fpbg_ffdeq.ma".

(* PROPER PARALLEL RST-COMPUTATION FOR CLOSURES **************************)

lemma lpxs_fpbg: ∀h,o,G,L1,L2,T. ⦃G, L1⦄ ⊢ ➡*[h, o] L2 →
                 (L1 ≡[T, 0] L2 → ⊥) → ⦃G, L1, T⦄ >≛[h, o] ⦃G, L2, T⦄.
#h #o #G #L1 #L2 #T #H #H0 elim (lpxs_nlleq_inv_step_sn … H … H0) -H -H0
/4 width=5 by fpb_lpx, lpxs_lleq_fpbs, ex2_3_intro/
qed.
