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

include "basic_2/rt_transition/lpx_rdeq.ma".
include "basic_2/rt_computation/rsx.ma".

(* STRONGLY NORMALIZING REFERRED LOCAL ENV.S FOR UNBOUND RT-TRANSITION ******)

(* Advanced properties ******************************************************)

(* Basic_2A1: uses: lsx_lleq_trans *)
lemma rsx_rdeq_trans (h) (G):
      ∀L1,T. G ⊢ ⬈*[h,T] 𝐒⦃L1⦄ →
      ∀L2. L1 ≛[T] L2 → G ⊢ ⬈*[h,T] 𝐒⦃L2⦄.
#h #G #L1 #T #H @(rsx_ind … H) -L1
#L1 #_ #IHL1 #L2 #HL12 @rsx_intro
#L #HL2 #HnL2 elim (rdeq_lpx_trans … HL2 … HL12) -HL2
/4 width=5 by rdeq_repl/
qed-.

(* Basic_2A1: uses: lsx_lpx_trans *)
lemma rsx_lpx_trans (h) (G):
      ∀L1,T. G ⊢ ⬈*[h,T] 𝐒⦃L1⦄ →
      ∀L2. ⦃G,L1⦄ ⊢ ⬈[h] L2 → G ⊢ ⬈*[h,T] 𝐒⦃L2⦄.
#h #G #L1 #T #H @(rsx_ind … H) -L1 #L1 #HL1 #IHL1 #L2 #HL12
elim (rdeq_dec L1 L2 T) /3 width=4 by rsx_rdeq_trans/
qed-.
