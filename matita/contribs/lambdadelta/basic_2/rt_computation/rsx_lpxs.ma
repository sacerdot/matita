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

include "basic_2/rt_computation/lpxs_reqg.ma".
include "basic_2/rt_computation/lpxs_lpxs.ma".
include "basic_2/rt_computation/rsx_rsx.ma".

(* STRONGLY NORMALIZING REFERRED LOCAL ENVS FOR EXTENDED RT-TRANSITION ******)

(* Properties with extended rt-computation for full local environments ******)

(* Basic_2A1: uses: lsx_intro_alt *)
lemma rsx_intro_lpxs (G):
      ∀L1,T. (∀L2. ❪G,L1❫ ⊢ ⬈* L2 → (L1 ≅[T] L2 → ⊥) → G ⊢ ⬈*𝐒[T] L2) →
      G ⊢ ⬈*𝐒[T] L1.
/4 width=1 by lpx_lpxs, rsx_intro/ qed-.

(* Basic_2A1: uses: lsx_lpxs_trans *)
lemma rsx_lpxs_trans (G):
      ∀L1,T. G ⊢ ⬈*𝐒[T] L1 →
      ∀L2. ❪G,L1❫ ⊢ ⬈* L2 → G ⊢ ⬈*𝐒[T] L2.
#G #L1 #T #HL1 #L2 #H @(lpxs_ind_dx … H) -L2
/2 width=3 by rsx_lpx_trans/
qed-.

(* Eliminators with extended rt-computation for full local environments *****)

lemma rsx_ind_lpxs_reqx (G) (T) (Q:predicate lenv):
      (∀L1. G ⊢ ⬈*𝐒[T] L1 →
        (∀L2. ❪G,L1❫ ⊢ ⬈* L2 → (L1 ≅[T] L2 → ⊥) → Q L2) →
        Q L1
      ) →
      ∀L1. G ⊢ ⬈*𝐒[T] L1 →
      ∀L0. ❪G,L1❫ ⊢ ⬈* L0 → ∀L2. L0 ≅[T] L2 → Q L2.
#G #T #Q #IH #L1 #H @(rsx_ind … H) -L1
#L1 #HL1 #IH1 #L0 #HL10 #L2 #HL02
@IH -IH /3 width=3 by rsx_lpxs_trans, rsx_reqx_trans/ -HL1 #K2 #HLK2 #HnLK2
lapply (reqg_rneqg_trans … HL02 … HnLK2) -HnLK2 // #H
elim (reqg_lpxs_trans … HLK2 … HL02) -L2 // #K0 #HLK0 #HK02
lapply (rneqg_reqg_canc_dx … H … HK02) -H // #HnLK0
elim (reqx_dec L1 L0 T) #H
[ lapply (reqg_rneqg_trans … H … HnLK0) -H -HnLK0 // #Hn10
  lapply (lpxs_trans … HL10 … HLK0) -L0 #H10
  elim (lpxs_rneqg_inv_step_sn … H10 …  Hn10) -H10 -Hn10
  /3 width=8 by reqg_trans, sfull_dec/
| elim (lpxs_rneqg_inv_step_sn … HL10 … H) -HL10 -H /2 width=1 by sfull_dec/ #L #K #HL1 #HnL1 #HLK #HKL0
  elim (reqg_lpxs_trans … HLK0 … HKL0) -L0
  /3 width=8 by lpxs_trans, reqg_trans/
]
qed-.

(* Basic_2A1: uses: lsx_ind_alt *)
lemma rsx_ind_lpxs (G) (T) (Q:predicate lenv):
      (∀L1. G ⊢ ⬈*𝐒[T] L1 →
        (∀L2. ❪G,L1❫ ⊢ ⬈* L2 → (L1 ≅[T] L2 → ⊥) → Q L2) →
        Q L1
      ) →
      ∀L. G ⊢ ⬈*𝐒[T] L → Q L.
#G #T #Q #IH #L #HL
@(rsx_ind_lpxs_reqx … IH … HL) -IH -HL
/2 width=3 by rex_refl/ (**) (* full auto fails *)
qed-.

(* Advanced properties ******************************************************)

fact rsx_bind_lpxs_aux (G):
     ∀p,I,L1,V. G ⊢ ⬈*𝐒[V] L1 →
     ∀Y,T. G ⊢ ⬈*𝐒[T] Y →
     ∀L2. Y = L2.ⓑ[I]V → ❪G,L1❫ ⊢ ⬈* L2 →
     G ⊢ ⬈*𝐒[ⓑ[p,I]V.T] L2.
#G #p #I #L1 #V #H @(rsx_ind_lpxs … H) -L1
#L1 #_ #IHL1 #Y #T #H @(rsx_ind_lpxs … H) -Y
#Y #HY #IHY #L2 #H #HL12 destruct
@rsx_intro_lpxs #L0 #HL20
lapply (lpxs_trans … HL12 … HL20) #HL10 #H
elim (rneqg_inv_bind … H) -H /2 width=1 by sfull_dec/ [ -IHY | -HY -IHL1 -HL12 ]
[ #HnV elim (reqx_dec L1 L2 V)
  [ #HV @(IHL1 … HL10) -IHL1 -HL12 -HL10
    /3 width=4 by rsx_lpxs_trans, lpxs_bind_refl_dx, reqg_canc_sn/ (**) (* full auto too slow *)
  | -HnV -HL10 /4 width=4 by rsx_lpxs_trans, lpxs_bind_refl_dx/
  ]
| /3 width=4 by lpxs_bind_refl_dx/
]
qed-.

(* Basic_2A1: uses: lsx_bind *)
lemma rsx_bind (G):
      ∀p,I,L,V. G ⊢ ⬈*𝐒[V] L →
      ∀T. G ⊢ ⬈*𝐒[T] L.ⓑ[I]V →
      G ⊢ ⬈*𝐒[ⓑ[p,I]V.T] L.
/2 width=3 by rsx_bind_lpxs_aux/ qed.

(* Basic_2A1: uses: lsx_flat_lpxs *)
lemma rsx_flat_lpxs (G):
      ∀I,L1,V. G ⊢ ⬈*𝐒[V] L1 →
      ∀L2,T. G ⊢ ⬈*𝐒[T] L2 → ❪G,L1❫ ⊢ ⬈* L2 →
      G ⊢ ⬈*𝐒[ⓕ[I]V.T] L2.
#G #I #L1 #V #H @(rsx_ind_lpxs … H) -L1
#L1 #HL1 #IHL1 #L2 #T #H @(rsx_ind_lpxs … H) -L2
#L2 #HL2 #IHL2 #HL12 @rsx_intro_lpxs
#L0 #HL20 lapply (lpxs_trans … HL12 … HL20)
#HL10 #H elim (rneqg_inv_flat … H) -H /2 width=1 by sfull_dec/ [ -HL1 -IHL2 | -HL2 -IHL1 ]
[ #HnV elim (reqx_dec L1 L2 V)
  [ #HV @(IHL1 … HL10) -IHL1 -HL12 -HL10
    /3 width=5 by rsx_lpxs_trans, reqg_canc_sn/ (**) (* full auto too slow: 47s *)
  | -HnV -HL10 /3 width=4 by rsx_lpxs_trans/
  ]
| /3 width=3 by/
]
qed-.

(* Basic_2A1: uses: lsx_flat *)
lemma rsx_flat (G):
      ∀I,L,V. G ⊢ ⬈*𝐒[V] L →
      ∀T. G ⊢ ⬈*𝐒[T] L → G ⊢ ⬈*𝐒[ⓕ[I]V.T] L.
/2 width=3 by rsx_flat_lpxs/ qed.

fact rsx_bind_lpxs_void_aux (G):
     ∀p,I,L1,V. G ⊢ ⬈*𝐒[V] L1 →
     ∀Y,T. G ⊢ ⬈*𝐒[T] Y →
     ∀L2. Y = L2.ⓧ → ❪G,L1❫ ⊢ ⬈* L2 →
     G ⊢ ⬈*𝐒[ⓑ[p,I]V.T] L2.
#G #p #I #L1 #V #H @(rsx_ind_lpxs … H) -L1
#L1 #_ #IHL1 #Y #T #H @(rsx_ind_lpxs … H) -Y
#Y #HY #IHY #L2 #H #HL12 destruct
@rsx_intro_lpxs #L0 #HL20
lapply (lpxs_trans … HL12 … HL20) #HL10 #H
elim (rneqg_inv_bind_void … H) -H /2 width=1 by sfull_dec/ [ -IHY | -HY -IHL1 -HL12 ]
[ #HnV elim (reqx_dec L1 L2 V)
  [ #HV @(IHL1 … HL10) -IHL1 -HL12 -HL10
    /3 width=6 by rsx_lpxs_trans, lpxs_bind_refl_dx, reqg_canc_sn/ (**) (* full auto too slow *)
  | -HnV -HL10 /4 width=4 by rsx_lpxs_trans, lpxs_bind_refl_dx/
  ]
| /3 width=4 by lpxs_bind_refl_dx/
]
qed-.

lemma rsx_bind_void (G):
      ∀p,I,L,V. G ⊢ ⬈*𝐒[V] L →
      ∀T. G ⊢ ⬈*𝐒[T] L.ⓧ →
      G ⊢ ⬈*𝐒[ⓑ[p,I]V.T] L.
/2 width=3 by rsx_bind_lpxs_void_aux/ qed.
