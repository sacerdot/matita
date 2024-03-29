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

include "static_2/static/reqg_drops.ma".
include "basic_2/rt_transition/lpx_drops.ma".
include "basic_2/rt_computation/rsx_length.ma".
include "basic_2/rt_computation/rsx_fqup.ma".

(* STRONGLY NORMALIZING REFERRED LOCAL ENVS FOR EXTENDED RT-TRANSITION ******)

(* Properties with generic relocation ***************************************)

(* Note: this uses length *)
(* Basic_2A1: uses: lsx_lift_le lsx_lift_ge *)
lemma rsx_lifts (G):
      d_liftable1_isuni … (λL,T. G ⊢ ⬈*𝐒[T] L).
#G #K #T #H @(rsx_ind … H) -K
#K1 #_ #IH #b #f #L1 #HLK1 #Hf #U #HTU @rsx_intro
#L2 #HL12 #HnL12 elim (lpx_drops_conf … HLK1 … HL12)
/5 width=9 by reqg_lifts_bi, lpx_fwd_length/
qed-.

(* Inversion lemmas on relocation *******************************************)

(* Basic_2A1: uses: lsx_inv_lift_le lsx_inv_lift_be lsx_inv_lift_ge *)
lemma rsx_inv_lifts (G):
      d_deliftable1_isuni … (λL,T. G ⊢ ⬈*𝐒[T] L).
#G #L #U #H @(rsx_ind … H) -L
#L1 #_ #IH #b #f #K1 #HLK1 #Hf #T #HTU @rsx_intro
#K2 #HK12 #HnK12 elim (drops_lpx_trans … HLK1 … HK12) -HK12
/4 width=10 by reqg_inv_lifts_bi/
qed-.

(* Advanced properties ******************************************************)

(* Basic_2A1: uses: lsx_lref_free *)
lemma rsx_lref_atom_drops (G):
      ∀L,i. ⇩*[ⓕ,𝐔❨i❩] L ≘ ⋆ → G ⊢ ⬈*𝐒[#i] L.
#G #L1 #i #HL1
@(rsx_lifts … (#0) … HL1) -HL1 //
qed.

(* Basic_2A1: uses: lsx_lref_skip *)
lemma rsx_lref_unit_drops (G):
      ∀I,L,K,i. ⇩[i] L ≘ K.ⓤ[I] → G ⊢ ⬈*𝐒[#i] L.
#G #I #L1 #K1 #i #HL1
@(rsx_lifts … (#0) … HL1) -HL1 //
qed.

(* Advanced forward lemmas **************************************************)

(* Basic_2A1: uses: lsx_fwd_lref_be *)
lemma rsx_fwd_lref_pair_drops (G):
      ∀L,i. G ⊢ ⬈*𝐒[#i] L →
      ∀I,K,V. ⇩[i] L ≘ K.ⓑ[I]V → G ⊢ ⬈*𝐒[V] K.
#G #L #i #HL #I #K #V #HLK
lapply (rsx_inv_lifts … HL … HLK … (#0) ?) -L
/2 width=2 by rsx_fwd_pair/
qed-.
