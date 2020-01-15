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

include "basic_2/rt_computation/lpxs_reqx.ma".
include "basic_2/rt_computation/lpxs_lpxs.ma".
include "basic_2/rt_computation/rsx_rsx.ma".

(* STRONGLY NORMALIZING REFERRED LOCAL ENV.S FOR UNBOUND RT-TRANSITION ******)

(* Properties with unbound rt-computation for full local environments *******)

(* Basic_2A1: uses: lsx_intro_alt *)
lemma rsx_intro_lpxs (h) (G):
      ∀L1,T. (∀L2. ❪G,L1❫ ⊢ ⬈*[h] L2 → (L1 ≛[T] L2 → ⊥) → G ⊢ ⬈*𝐒[h,T] L2) →
      G ⊢ ⬈*𝐒[h,T] L1.
/4 width=1 by lpx_lpxs, rsx_intro/ qed-.

(* Basic_2A1: uses: lsx_lpxs_trans *)
lemma rsx_lpxs_trans (h) (G):
      ∀L1,T. G ⊢ ⬈*𝐒[h,T] L1 →
      ∀L2. ❪G,L1❫ ⊢ ⬈*[h] L2 → G ⊢ ⬈*𝐒[h,T] L2.
#h #G #L1 #T #HL1 #L2 #H @(lpxs_ind_dx … H) -L2
/2 width=3 by rsx_lpx_trans/
qed-.

(* Eliminators with unbound rt-computation for full local environments ******)

lemma rsx_ind_lpxs_reqx (h) (G) (T) (Q:predicate lenv):
      (∀L1. G ⊢ ⬈*𝐒[h,T] L1 →
        (∀L2. ❪G,L1❫ ⊢ ⬈*[h] L2 → (L1 ≛[T] L2 → ⊥) → Q L2) →
        Q L1
      ) →
      ∀L1. G ⊢ ⬈*𝐒[h,T] L1 →
      ∀L0. ❪G,L1❫ ⊢ ⬈*[h] L0 → ∀L2. L0 ≛[T] L2 → Q L2.
#h #G #T #Q #IH #L1 #H @(rsx_ind … H) -L1
#L1 #HL1 #IH1 #L0 #HL10 #L2 #HL02
@IH -IH /3 width=3 by rsx_lpxs_trans, rsx_reqx_trans/ -HL1 #K2 #HLK2 #HnLK2
lapply (reqx_rneqx_trans … HL02 … HnLK2) -HnLK2 #H
elim (reqx_lpxs_trans … HLK2 … HL02) -L2 #K0 #HLK0 #HK02
lapply (rneqx_reqx_canc_dx … H … HK02) -H #HnLK0
elim (reqx_dec L1 L0 T) #H
[ lapply (reqx_rneqx_trans … H … HnLK0) -H -HnLK0 #Hn10
  lapply (lpxs_trans … HL10 … HLK0) -L0 #H10
  elim (lpxs_rneqx_inv_step_sn … H10 …  Hn10) -H10 -Hn10
  /3 width=8 by reqx_trans/
| elim (lpxs_rneqx_inv_step_sn … HL10 … H) -HL10 -H #L #K #HL1 #HnL1 #HLK #HKL0
  elim (reqx_lpxs_trans … HLK0 … HKL0) -L0
  /3 width=8 by lpxs_trans, reqx_trans/
]
qed-.

(* Basic_2A1: uses: lsx_ind_alt *)
lemma rsx_ind_lpxs (h) (G) (T) (Q:predicate lenv):
      (∀L1. G ⊢ ⬈*𝐒[h,T] L1 →
        (∀L2. ❪G,L1❫ ⊢ ⬈*[h] L2 → (L1 ≛[T] L2 → ⊥) → Q L2) →
        Q L1
      ) →
      ∀L. G ⊢ ⬈*𝐒[h,T] L → Q L.
#h #G #T #Q #IH #L #HL
@(rsx_ind_lpxs_reqx … IH … HL) -IH -HL // (**) (* full auto fails *)
qed-.

(* Advanced properties ******************************************************)

fact rsx_bind_lpxs_aux (h) (G):
     ∀p,I,L1,V. G ⊢ ⬈*𝐒[h,V] L1 →
     ∀Y,T. G ⊢ ⬈*𝐒[h,T] Y →
     ∀L2. Y = L2.ⓑ[I]V → ❪G,L1❫ ⊢ ⬈*[h] L2 →
     G ⊢ ⬈*𝐒[h,ⓑ[p,I]V.T] L2.
#h #G #p #I #L1 #V #H @(rsx_ind_lpxs … H) -L1
#L1 #_ #IHL1 #Y #T #H @(rsx_ind_lpxs … H) -Y
#Y #HY #IHY #L2 #H #HL12 destruct
@rsx_intro_lpxs #L0 #HL20
lapply (lpxs_trans … HL12 … HL20) #HL10 #H
elim (rneqx_inv_bind … H) -H [ -IHY | -HY -IHL1 -HL12 ]
[ #HnV elim (reqx_dec L1 L2 V)
  [ #HV @(IHL1 … HL10) -IHL1 -HL12 -HL10
    /3 width=4 by rsx_lpxs_trans, lpxs_bind_refl_dx, reqx_canc_sn/ (**) (* full auto too slow *)
  | -HnV -HL10 /4 width=4 by rsx_lpxs_trans, lpxs_bind_refl_dx/
  ]
| /3 width=4 by lpxs_bind_refl_dx/
]
qed-.

(* Basic_2A1: uses: lsx_bind *)
lemma rsx_bind (h) (G):
      ∀p,I,L,V. G ⊢ ⬈*𝐒[h,V] L →
      ∀T. G ⊢ ⬈*𝐒[h,T] L.ⓑ[I]V →
      G ⊢ ⬈*𝐒[h,ⓑ[p,I]V.T] L.
/2 width=3 by rsx_bind_lpxs_aux/ qed.

(* Basic_2A1: uses: lsx_flat_lpxs *)
lemma rsx_flat_lpxs (h) (G):
      ∀I,L1,V. G ⊢ ⬈*𝐒[h,V] L1 →
      ∀L2,T. G ⊢ ⬈*𝐒[h,T] L2 → ❪G,L1❫ ⊢ ⬈*[h] L2 →
      G ⊢ ⬈*𝐒[h,ⓕ[I]V.T] L2.
#h #G #I #L1 #V #H @(rsx_ind_lpxs … H) -L1
#L1 #HL1 #IHL1 #L2 #T #H @(rsx_ind_lpxs … H) -L2
#L2 #HL2 #IHL2 #HL12 @rsx_intro_lpxs
#L0 #HL20 lapply (lpxs_trans … HL12 … HL20)
#HL10 #H elim (rneqx_inv_flat … H) -H [ -HL1 -IHL2 | -HL2 -IHL1 ]
[ #HnV elim (reqx_dec L1 L2 V)
  [ #HV @(IHL1 … HL10) -IHL1 -HL12 -HL10
    /3 width=5 by rsx_lpxs_trans, reqx_canc_sn/ (**) (* full auto too slow: 47s *)
  | -HnV -HL10 /3 width=4 by rsx_lpxs_trans/
  ]
| /3 width=3 by/
]
qed-.

(* Basic_2A1: uses: lsx_flat *)
lemma rsx_flat (h) (G):
      ∀I,L,V. G ⊢ ⬈*𝐒[h,V] L →
      ∀T. G ⊢ ⬈*𝐒[h,T] L → G ⊢ ⬈*𝐒[h,ⓕ[I]V.T] L.
/2 width=3 by rsx_flat_lpxs/ qed.

fact rsx_bind_lpxs_void_aux (h) (G):
     ∀p,I,L1,V. G ⊢ ⬈*𝐒[h,V] L1 →
     ∀Y,T. G ⊢ ⬈*𝐒[h,T] Y →
     ∀L2. Y = L2.ⓧ → ❪G,L1❫ ⊢ ⬈*[h] L2 →
     G ⊢ ⬈*𝐒[h,ⓑ[p,I]V.T] L2.
#h #G #p #I #L1 #V #H @(rsx_ind_lpxs … H) -L1
#L1 #_ #IHL1 #Y #T #H @(rsx_ind_lpxs … H) -Y
#Y #HY #IHY #L2 #H #HL12 destruct
@rsx_intro_lpxs #L0 #HL20
lapply (lpxs_trans … HL12 … HL20) #HL10 #H
elim (rneqx_inv_bind_void … H) -H [ -IHY | -HY -IHL1 -HL12 ]
[ #HnV elim (reqx_dec L1 L2 V)
  [ #HV @(IHL1 … HL10) -IHL1 -HL12 -HL10
    /3 width=6 by rsx_lpxs_trans, lpxs_bind_refl_dx, reqx_canc_sn/ (**) (* full auto too slow *)
  | -HnV -HL10 /4 width=4 by rsx_lpxs_trans, lpxs_bind_refl_dx/
  ]
| /3 width=4 by lpxs_bind_refl_dx/
]
qed-.

lemma rsx_bind_void (h) (G):
      ∀p,I,L,V. G ⊢ ⬈*𝐒[h,V] L →
      ∀T. G ⊢ ⬈*𝐒[h,T] L.ⓧ →
      G ⊢ ⬈*𝐒[h,ⓑ[p,I]V.T] L.
/2 width=3 by rsx_bind_lpxs_void_aux/ qed.
