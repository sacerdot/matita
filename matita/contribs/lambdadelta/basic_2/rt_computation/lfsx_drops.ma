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

include "basic_2/static/lfdeq_length.ma".
include "basic_2/static/lfdeq_drops.ma".
include "basic_2/rt_transition/lfpx_length.ma".
include "basic_2/rt_transition/lfpx_drops.ma".
include "basic_2/rt_computation/lfsx_fqup.ma".

(* STRONGLY NORMALIZING LOCAL ENV.S FOR UNCOUNTED PARALLEL RT-TRANSITION ****)

(* Properties with generic relocation ***************************************)

(* Note: this uses length *)
(* Basic_2A1: uses: lsx_lift_le lsx_lift_ge *)
lemma lfsx_lifts: ∀h,o,G. d_liftable1_isuni … (λL,T. G ⊢ ⬈*[h, o, T] 𝐒⦃L⦄).
#h #o #G #K #T #H @(lfsx_ind … H) -K
#K1 #_ #IH #b #f #L1 #HLK1 #Hf #U #HTU @lfsx_intro
#L2 #HL12 #HnL12 elim (lfpx_drops_conf … HLK1 … HL12 … HTU)
/5 width=9 by lfdeq_lifts_bi, lfpx_fwd_length/
qed-.

(* Inversion lemmas on relocation *******************************************)

(* Basic_2A1: uses: lsx_inv_lift_le lsx_inv_lift_be lsx_inv_lift_ge *)
lemma lfsx_inv_lifts: ∀h,o,G. d_deliftable1_isuni … (λL,T. G ⊢ ⬈*[h, o, T] 𝐒⦃L⦄).
#h #o #G #L #U #H @(lfsx_ind … H) -L
#L1 #_ #IH #b #f #K1 #HLK1 #Hf #T #HTU @lfsx_intro
#K2 #HK12 #HnK12 elim (drops_lfpx_trans … HLK1 … HK12 … HTU) -HK12
/4 width=10 by lfdeq_inv_lifts_bi/
qed-.

(* Advanced properties ******************************************************)

(* Basic_2A1: uses: lsx_lref_free *)
lemma lfsx_lref_atom: ∀h,o,G,L,i. ⬇*[Ⓕ, 𝐔❴i❵] L ≘ ⋆ → G ⊢ ⬈*[h, o, #i] 𝐒⦃L⦄.
#h #o #G #L1 #i #HL1
@(lfsx_lifts … (#0) … HL1) -HL1 //
qed.

(* Basic_2A1: uses: lsx_lref_skip *)
lemma lfsx_lref_unit: ∀h,o,I,G,L,K,i. ⬇*[i] L ≘ K.ⓤ{I} → G ⊢ ⬈*[h, o, #i] 𝐒⦃L⦄.
#h #o #I #G #L1 #K1 #i #HL1
@(lfsx_lifts … (#0) … HL1) -HL1 //
qed.

(* Advanced forward lemmas **************************************************)

(* Basic_2A1: uses: lsx_fwd_lref_be *)
lemma lfsx_fwd_lref_pair: ∀h,o,G,L,i. G ⊢ ⬈*[h, o, #i] 𝐒⦃L⦄ →
                          ∀I,K,V. ⬇*[i] L ≘ K.ⓑ{I}V → G ⊢ ⬈*[h, o, V] 𝐒⦃K⦄.
#h #o #G #L #i #HL #I #K #V #HLK
lapply (lfsx_inv_lifts … HL … HLK … (#0) ?) -L
/2 width=2 by lfsx_fwd_pair/
qed-.
