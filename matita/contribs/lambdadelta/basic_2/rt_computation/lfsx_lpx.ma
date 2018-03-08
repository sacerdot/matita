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

include "basic_2/static/lfdeq_lfeq.ma".
include "basic_2/rt_transition/lfpx_lpx.ma".
include "basic_2/rt_computation/lfsx_lfsx.ma".

(* STRONGLY NORMALIZING LOCAL ENV.S FOR UNCOUNTED PARALLEL RT-TRANSITION ****)

(* Properties with uncounted rt-transition **********************************)

lemma lfsx_intro_lpx: ∀h,o,G,L1,T.
                      (∀L2. ⦃G, L1⦄ ⊢ ⬈[h] L2 → (L1 ≛[h, o, T] L2 → ⊥) → G ⊢ ⬈*[h, o, T] 𝐒⦃L2⦄) →
                      G ⊢ ⬈*[h, o, T] 𝐒⦃L1⦄.
#h #o #G #L1 #T #HT
@lfsx_intro #L2 #H
elim (lfpx_inv_lpx_lfeq … H) -H
/6 width=3 by lfsx_lfdeq_trans, lfdeq_trans, lfeq_lfdeq/
qed-.

lemma lfsx_lpx_trans: ∀h,o,G,L1,T. G ⊢ ⬈*[h, o, T] 𝐒⦃L1⦄ →
                      ∀L2. ⦃G, L1⦄ ⊢ ⬈[h] L2 → G ⊢ ⬈*[h, o, T] 𝐒⦃L2⦄.
/3 width=3 by lfsx_lfpx_trans, lfpx_lpx/ qed-.

(* Eliminators with uncounted rt-transition *********************************)

lemma lfsx_ind_lpx: ∀h,o,G,T. ∀R:predicate lenv.
                    (∀L1. G ⊢ ⬈*[h, o, T] 𝐒⦃L1⦄ →
                          (∀L2. ⦃G, L1⦄ ⊢ ⬈[h] L2 → (L1 ≛[h, o, T] L2 → ⊥) → R L2) →
                          R L1
                    ) →
                    ∀L. G ⊢ ⬈*[h, o, T] 𝐒⦃L⦄  → R L.
/5 width=6 by lfsx_ind, lfpx_lpx/ qed-.
