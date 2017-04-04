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

include "basic_2/static/lfdeq_lfdeq.ma".
include "basic_2/rt_transition/lfpx_lfdeq.ma".
include "basic_2/rt_computation/lfsx.ma".

(* STRONGLY NORMALIZING LOCAL ENV.S FOR UNCOUNTED PARALLEL RT-TRANSITION ****)

axiom pippo: ∀h,o,p,I,G,L1,L2,V,T. ⦃G, L1⦄ ⊢ ⬈[h, V] L2 →
             ∃∃L. ⦃G, L1⦄ ⊢ ⬈[h, ⓑ{p,I}V.T] L & L ≡[h, o, V] L2.

(* Advanced properties ******************************************************)

lemma lfsx_lfdeq_trans: ∀h,o,G,L1,T. G ⊢ ⬈*[h, o, T] 𝐒⦃L1⦄ →
                        ∀L2. L1 ≡[h, o, T] L2 → G ⊢ ⬈*[h, o, T] 𝐒⦃L2⦄.
#h #o #G #L1 #T #H @(lfsx_ind … H) -L1
#L1 #_ #IHL1 #L2 #HL12 @lfsx_intro
#L #HL2 #HnL2 elim (lfdeq_lfpx_trans … HL2 … HL12) -HL2
/4 width=5 by lfdeq_repl/
qed-.

(* Advanced forward lemmas **************************************************)

(* Basic_2A1: was: lsx_fwd_bind_sn *)
lemma lfsx_fwd_bind_sn: ∀h,o,p,I,G,L,V,T. G ⊢ ⬈*[h, o, ⓑ{p,I}V.T] 𝐒⦃L⦄ →
                        G ⊢ ⬈*[h, o, V] 𝐒⦃L⦄.
#h #o #p #I #G #L #V #T #H @(lfsx_ind … H) -L
#L1 #_ #IHL1 @lfsx_intro
#L2 #H #HnL12 elim (pippo … o p I … T H) -H
/6 width=4 by lfsx_lfdeq_trans, lfdeq_trans, lfdeq_fwd_bind_sn/
qed-.
(*
lemma lfsx_fwd_flat_sn: ∀h,o,I,G,L,V,T,l. G ⊢ ⬈*[h, o, ⓕ{I}V.T, l] L →
                       G ⊢ ⬈*[h, o, V, l] L.
#h #o #I #G #L #V #T #l #H @(lfsx_ind … H) -L
#L1 #_ #IHL1 @lfsx_intro
#L2 #HL12 #HV @IHL1 /3 width=3 by lfdeq_fwd_flat_sn/
qed-.

lemma lfsx_fwd_flat_dx: ∀h,o,I,G,L,V,T,l. G ⊢ ⬈*[h, o, ⓕ{I}V.T, l] L →
                       G ⊢ ⬈*[h, o, T, l] L.
#h #o #I #G #L #V #T #l #H @(lfsx_ind … H) -L
#L1 #_ #IHL1 @lfsx_intro
#L2 #HL12 #HV @IHL1 /3 width=3 by lfdeq_fwd_flat_dx/
qed-.

lemma lfsx_fwd_pair_sn: ∀h,o,I,G,L,V,T,l. G ⊢ ⬈*[h, o, ②{I}V.T, l] L →
                       G ⊢ ⬈*[h, o, V, l] L.
#h #o * /2 width=4 by lfsx_fwd_bind_sn, lfsx_fwd_flat_sn/
qed-.

(* Basic inversion lemmas ***************************************************)

lemma lfsx_inv_flat: ∀h,o,I,G,L,V,T,l. G ⊢ ⬈*[h, o, ⓕ{I}V.T, l] L →
                    G ⊢ ⬈*[h, o, V, l] L ∧ G ⊢ ⬈*[h, o, T, l] L.
/3 width=3 by lfsx_fwd_flat_sn, lfsx_fwd_flat_dx, conj/ qed-.
*)