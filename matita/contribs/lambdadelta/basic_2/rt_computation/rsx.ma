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

include "basic_2/notation/relations/predtysnstrong_4.ma".
include "static_2/static/reqx.ma".
include "basic_2/rt_transition/lpx.ma".

(* STRONGLY NORMALIZING REFERRED LOCAL ENV.S FOR UNBOUND RT-TRANSITION ******)

definition rsx (h) (G) (T): predicate lenv ≝
           SN … (lpx h G) (reqx T).

interpretation
   "strong normalization for unbound context-sensitive parallel rt-transition on referred entries (local environment)"
   'PRedTySNStrong h T G L = (rsx h G T L).

(* Basic eliminators ********************************************************)

(* Basic_2A1: uses: lsx_ind *)
lemma rsx_ind (h) (G) (T) (Q:predicate lenv):
      (∀L1. G ⊢ ⬈*[h,T] 𝐒❪L1❫ →
            (∀L2. ❪G,L1❫ ⊢ ⬈[h] L2 → (L1 ≛[T] L2 → ⊥) → Q L2) →
            Q L1
      ) →
      ∀L. G ⊢ ⬈*[h,T] 𝐒❪L❫ →  Q L.
#h #G #T #Q #H0 #L1 #H elim H -L1
/5 width=1 by SN_intro/
qed-.

(* Basic properties *********************************************************)

(* Basic_2A1: uses: lsx_intro *)
lemma rsx_intro (h) (G) (T):
      ∀L1.
      (∀L2. ❪G,L1❫ ⊢ ⬈[h] L2 → (L1 ≛[T] L2 → ⊥) → G ⊢ ⬈*[h,T] 𝐒❪L2❫) →
      G ⊢ ⬈*[h,T] 𝐒❪L1❫.
/5 width=1 by SN_intro/ qed.

(* Basic forward lemmas *****************************************************)

(* Basic_2A1: uses: lsx_fwd_pair_sn lsx_fwd_bind_sn lsx_fwd_flat_sn *)
lemma rsx_fwd_pair_sn (h) (G):
      ∀I,L,V,T. G ⊢ ⬈*[h,②[I]V.T] 𝐒❪L❫ →
      G ⊢ ⬈*[h,V] 𝐒❪L❫.
#h #G #I #L #V #T #H
@(rsx_ind … H) -L #L1 #_ #IHL1
@rsx_intro #L2 #HL12 #HnL12
/4 width=3 by reqx_fwd_pair_sn/
qed-.

(* Basic_2A1: uses: lsx_fwd_flat_dx *)
lemma rsx_fwd_flat_dx (h) (G):
      ∀I,L,V,T. G ⊢ ⬈*[h,ⓕ[I]V.T] 𝐒❪L❫ →
      G ⊢ ⬈*[h,T] 𝐒❪L❫.
#h #G #I #L #V #T #H
@(rsx_ind … H) -L #L1 #_ #IHL1
@rsx_intro #L2 #HL12 #HnL12
/4 width=3 by reqx_fwd_flat_dx/
qed-.

fact rsx_fwd_pair_aux (h) (G):
     ∀L. G ⊢ ⬈*[h,#0] 𝐒❪L❫ →
     ∀I,K,V. L = K.ⓑ[I]V → G ⊢ ⬈*[h,V] 𝐒❪K❫.
#h #G #L #H
@(rsx_ind … H) -L #L1 #_ #IH #I #K1 #V #H destruct
/5 width=5 by lpx_pair, rsx_intro, reqx_fwd_zero_pair/
qed-.

lemma rsx_fwd_pair (h) (G):
      ∀I,K,V. G ⊢ ⬈*[h,#0] 𝐒❪K.ⓑ[I]V❫ → G ⊢ ⬈*[h,V] 𝐒❪K❫.
/2 width=4 by rsx_fwd_pair_aux/ qed-.

(* Basic inversion lemmas ***************************************************)

(* Basic_2A1: uses: lsx_inv_flat *)
lemma rsx_inv_flat (h) (G):
      ∀I,L,V,T. G ⊢ ⬈*[h,ⓕ[I]V.T] 𝐒❪L❫ →
      ∧∧ G ⊢ ⬈*[h,V] 𝐒❪L❫ & G ⊢ ⬈*[h,T] 𝐒❪L❫.
/3 width=3 by rsx_fwd_pair_sn, rsx_fwd_flat_dx, conj/ qed-.

(* Basic_2A1: removed theorems 9:
              lsx_ge_up lsx_ge
              lsxa_ind lsxa_intro lsxa_lleq_trans lsxa_lpxs_trans lsxa_intro_lpx lsx_lsxa lsxa_inv_lsx
*)
