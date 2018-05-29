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

include "basic_2/rt_transition/lpx_lfdeq.ma".
include "basic_2/rt_computation/rdsx.ma".

(* STRONGLY NORMALIZING REFERRED LOCAL ENV.S FOR UNBOUND RT-TRANSITION ******)

(* Advanced properties ******************************************************)

(* Basic_2A1: uses: lsx_lleq_trans *)
lemma rdsx_lfdeq_trans (h) (o) (G):
                       ∀L1,T. G ⊢ ⬈*[h, o, T] 𝐒⦃L1⦄ →
                       ∀L2. L1 ≛[h, o, T] L2 → G ⊢ ⬈*[h, o, T] 𝐒⦃L2⦄.
#h #o #G #L1 #T #H @(rdsx_ind … H) -L1
#L1 #_ #IHL1 #L2 #HL12 @rdsx_intro
#L #HL2 #HnL2 elim (lfdeq_lpx_trans … HL2 … HL12) -HL2
/4 width=5 by lfdeq_repl/
qed-.

(* Basic_2A1: uses: lsx_lpx_trans *)
lemma rdsx_lpx_trans (h) (o) (G):
                     ∀L1,T. G ⊢ ⬈*[h, o, T] 𝐒⦃L1⦄ →
                     ∀L2. ⦃G, L1⦄ ⊢ ⬈[h] L2 → G ⊢ ⬈*[h, o, T] 𝐒⦃L2⦄.
#h #o #G #L1 #T #H @(rdsx_ind … H) -L1 #L1 #HL1 #IHL1 #L2 #HL12
elim (lfdeq_dec h o L1 L2 T) /3 width=4 by rdsx_lfdeq_trans/
qed-.
