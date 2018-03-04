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

include "basic_2/rt_transition/lfpx_lfdeq.ma".
include "basic_2/rt_computation/lfsx.ma".

(* STRONGLY NORMALIZING LOCAL ENV.S FOR UNCOUNTED PARALLEL RT-TRANSITION ****)

(* Advanced properties ******************************************************)

(* Basic_2A1: uses: lsx_lleq_trans *)
lemma lfsx_lfdeq_trans: ∀h,o,G,L1,T. G ⊢ ⬈*[h, o, T] 𝐒⦃L1⦄ →
                        ∀L2. L1 ≛[h, o, T] L2 → G ⊢ ⬈*[h, o, T] 𝐒⦃L2⦄.
#h #o #G #L1 #T #H @(lfsx_ind … H) -L1
#L1 #_ #IHL1 #L2 #HL12 @lfsx_intro
#L #HL2 #HnL2 elim (lfdeq_lfpx_trans … HL2 … HL12) -HL2
/4 width=5 by lfdeq_repl/
qed-.

(* Basic_2A1: uses: lsx_lpx_trans *)
lemma lfsx_lfpx_trans: ∀h,o,G,L1,T. G ⊢ ⬈*[h, o, T] 𝐒⦃L1⦄ →
                       ∀L2. ⦃G, L1⦄ ⊢ ⬈[h, T] L2 → G ⊢ ⬈*[h, o, T] 𝐒⦃L2⦄.
#h #o #G #L1 #T #H @(lfsx_ind … H) -L1 #L1 #HL1 #IHL1 #L2 #HL12
elim (lfdeq_dec h o L1 L2 T) /3 width=4 by lfsx_lfdeq_trans, lfxs_refl/
qed-.

(* Advanced forward lemmas **************************************************)

(* Basic_2A1: uses: lsx_fwd_pair_sn lsx_fwd_bind_sn lsx_fwd_flat_sn *)
lemma lfsx_fwd_pair_sn: ∀h,o,I,G,L,V,T. G ⊢ ⬈*[h, o, ②{I}V.T] 𝐒⦃L⦄ →
                        G ⊢ ⬈*[h, o, V] 𝐒⦃L⦄.
#h #o #I #G #L #V #T #H @(lfsx_ind … H) -L
#L1 #_ #IHL1 @lfsx_intro
#L2 #H #HnL12 elim (lfpx_pair_sn_split … H o I T) -H
/6 width=3 by lfsx_lfdeq_trans, lfdeq_trans, lfdeq_fwd_pair_sn/
qed-.

(* Basic_2A1: uses: lsx_fwd_flat_dx *)
lemma lfsx_fwd_flat_dx: ∀h,o,I,G,L,V,T. G ⊢ ⬈*[h, o, ⓕ{I}V.T] 𝐒⦃L⦄ →
                        G ⊢ ⬈*[h, o, T] 𝐒⦃L⦄.
#h #o #I #G #L #V #T #H @(lfsx_ind … H) -L
#L1 #_ #IHL1 @lfsx_intro
#L2 #H #HnL12 elim (lfpx_flat_dx_split … H o I V) -H
/6 width=3 by lfsx_lfdeq_trans, lfdeq_trans, lfdeq_fwd_flat_dx/
qed-.

(* Basic_2A1: uses: lsx_fwd_bind_dx *)
(* Note: the exclusion binder (ⓧ) makes this more elegant and much simpler *)
lemma lfsx_fwd_bind_dx: ∀h,o,p,I,G,L,V,T. G ⊢ ⬈*[h, o, ⓑ{p,I}V.T] 𝐒⦃L⦄ →
                        G ⊢ ⬈*[h, o, T] 𝐒⦃L.ⓧ⦄.
#h #o #p #I #G #L #V #T #H @(lfsx_ind … H) -L
#L1 #_ #IH @lfsx_intro
#L2 #H #HT elim (lfpx_bind_dx_split_void … H o p I V) -H
/6 width=5 by lfsx_lfdeq_trans, lfdeq_trans, lfdeq_fwd_bind_dx_void/
qed-.

(* Advanced inversion lemmas ************************************************)

(* Basic_2A1: uses: lsx_inv_flat *)
lemma lfsx_inv_flat: ∀h,o,I,G,L,V,T. G ⊢ ⬈*[h, o, ⓕ{I}V.T] 𝐒⦃L⦄ →
                     G ⊢ ⬈*[h, o, V] 𝐒⦃L⦄ ∧ G ⊢ ⬈*[h, o, T] 𝐒⦃L⦄.
/3 width=3 by lfsx_fwd_pair_sn, lfsx_fwd_flat_dx, conj/ qed-.

(* Basic_2A1: uses: lsx_inv_bind *)
lemma lfsx_inv_bind: ∀h,o,p,I,G,L,V,T. G ⊢ ⬈*[h, o, ⓑ{p,I}V.T] 𝐒⦃L⦄ →
                     G ⊢ ⬈*[h, o, V] 𝐒⦃L⦄ ∧ G ⊢ ⬈*[h, o, T] 𝐒⦃L.ⓧ⦄.
/3 width=4 by lfsx_fwd_pair_sn, lfsx_fwd_bind_dx, conj/ qed-.
