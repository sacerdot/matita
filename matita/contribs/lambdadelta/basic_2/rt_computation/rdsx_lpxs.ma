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

include "basic_2/rt_computation/lpxs_lfdeq.ma".
include "basic_2/rt_computation/lpxs_lpxs.ma".
include "basic_2/rt_computation/rdsx_rdsx.ma".

(* STRONGLY NORMALIZING REFERRED LOCAL ENV.S FOR UNBOUND RT-TRANSITION ******)

(* Properties with unbound rt-computation for full local environments *******)

(* Basic_2A1: uses: lsx_intro_alt *)
lemma rdsx_intro_lpxs (h) (o) (G):
                      ∀L1,T. (∀L2. ⦃G, L1⦄ ⊢ ⬈*[h] L2 → (L1 ≛[h, o, T] L2 → ⊥) → G ⊢ ⬈*[h, o, T] 𝐒⦃L2⦄) →
                      G ⊢ ⬈*[h, o, T] 𝐒⦃L1⦄.
/4 width=1 by lpx_lpxs, rdsx_intro/ qed-.

(* Basic_2A1: uses: lsx_lpxs_trans *)
lemma rdsx_lpxs_trans (h) (o) (G): ∀L1,T. G ⊢ ⬈*[h, o, T] 𝐒⦃L1⦄ →
                                   ∀L2. ⦃G, L1⦄ ⊢ ⬈*[h] L2 → G ⊢ ⬈*[h, o, T] 𝐒⦃L2⦄.
#h #o #G #L1 #T #HL1 #L2 #H @(lpxs_ind_dx … H) -L2
/2 width=3 by rdsx_lpx_trans/
qed-.

(* Eliminators with unbound rt-computation for full local environments ******)

lemma rdsx_ind_lpxs_lfdeq (h) (o) (G):
                          ∀T. ∀Q:predicate lenv.
                          (∀L1. G ⊢ ⬈*[h, o, T] 𝐒⦃L1⦄ →
                                (∀L2. ⦃G, L1⦄ ⊢ ⬈*[h] L2 → (L1 ≛[h, o, T] L2 → ⊥) → Q L2) →
                                Q L1
                          ) →
                          ∀L1. G ⊢ ⬈*[h, o, T] 𝐒⦃L1⦄  →
                          ∀L0. ⦃G, L1⦄ ⊢ ⬈*[h] L0 → ∀L2. L0 ≛[h, o, T] L2 → Q L2.
#h #o #G #T #Q #IH #L1 #H @(rdsx_ind … H) -L1
#L1 #HL1 #IH1 #L0 #HL10 #L2 #HL02
@IH -IH /3 width=3 by rdsx_lpxs_trans, rdsx_lfdeq_trans/ -HL1 #K2 #HLK2 #HnLK2
lapply (lfdeq_lfdneq_trans … HL02 … HnLK2) -HnLK2 #H
elim (lfdeq_lpxs_trans … HLK2 … HL02) -L2 #K0 #HLK0 #HK02
lapply (lfdneq_lfdeq_canc_dx … H … HK02) -H #HnLK0
elim (lfdeq_dec h o L1 L0 T) #H
[ lapply (lfdeq_lfdneq_trans … H … HnLK0) -H -HnLK0 #Hn10
  lapply (lpxs_trans … HL10 … HLK0) -L0 #H10
  elim (lpxs_lfdneq_inv_step_sn … H10 …  Hn10) -H10 -Hn10
  /3 width=8 by lfdeq_trans/
| elim (lpxs_lfdneq_inv_step_sn … HL10 … H) -HL10 -H #L #K #HL1 #HnL1 #HLK #HKL0
  elim (lfdeq_lpxs_trans … HLK0 … HKL0) -L0
  /3 width=8 by lpxs_trans, lfdeq_trans/
]
qed-.

(* Basic_2A1: uses: lsx_ind_alt *)
lemma rdsx_ind_lpxs (h) (o) (G):
                    ∀T. ∀Q:predicate lenv.
                    (∀L1. G ⊢ ⬈*[h, o, T] 𝐒⦃L1⦄ →
                          (∀L2. ⦃G, L1⦄ ⊢ ⬈*[h] L2 → (L1 ≛[h, o, T] L2 → ⊥) → Q L2) →
                          Q L1
                    ) →
                    ∀L. G ⊢ ⬈*[h, o, T] 𝐒⦃L⦄  → Q L.
#h #o #G #T #Q #IH #L #HL
@(rdsx_ind_lpxs_lfdeq … IH … HL) -IH -HL // (**) (* full auto fails *)
qed-.

(* Advanced properties ******************************************************)

fact rdsx_bind_lpxs_aux (h) (o) (G):
                        ∀p,I,L1,V. G ⊢ ⬈*[h, o, V] 𝐒⦃L1⦄ →
                        ∀Y,T. G ⊢ ⬈*[h, o, T] 𝐒⦃Y⦄ →
                        ∀L2. Y = L2.ⓑ{I}V → ⦃G, L1⦄ ⊢ ⬈*[h] L2 →
                        G ⊢ ⬈*[h, o, ⓑ{p,I}V.T] 𝐒⦃L2⦄.
#h #o #G #p #I #L1 #V #H @(rdsx_ind_lpxs … H) -L1
#L1 #_ #IHL1 #Y #T #H @(rdsx_ind_lpxs … H) -Y
#Y #HY #IHY #L2 #H #HL12 destruct
@rdsx_intro_lpxs #L0 #HL20
lapply (lpxs_trans … HL12 … HL20) #HL10 #H
elim (lfdneq_inv_bind … H) -H [ -IHY | -HY -IHL1 -HL12 ]
[ #HnV elim (lfdeq_dec h o L1 L2 V)
  [ #HV @(IHL1 … HL10) -IHL1 -HL12 -HL10
    /3 width=4 by rdsx_lpxs_trans, lpxs_bind_refl_dx, lfdeq_canc_sn/ (**) (* full auto too slow *)
  | -HnV -HL10 /4 width=4 by rdsx_lpxs_trans, lpxs_bind_refl_dx/
  ]
| /3 width=4 by lpxs_bind_refl_dx/
]
qed-.

(* Basic_2A1: uses: lsx_bind *)
lemma rdsx_bind (h) (o) (G):
                ∀p,I,L,V. G ⊢ ⬈*[h, o, V] 𝐒⦃L⦄ →
                ∀T. G ⊢ ⬈*[h, o, T] 𝐒⦃L.ⓑ{I}V⦄ →
                G ⊢ ⬈*[h, o, ⓑ{p,I}V.T] 𝐒⦃L⦄.
/2 width=3 by rdsx_bind_lpxs_aux/ qed.

(* Basic_2A1: uses: lsx_flat_lpxs *)
lemma rdsx_flat_lpxs (h) (o) (G):
                     ∀I,L1,V. G ⊢ ⬈*[h, o, V] 𝐒⦃L1⦄ →
                     ∀L2,T. G ⊢ ⬈*[h, o, T] 𝐒⦃L2⦄ → ⦃G, L1⦄ ⊢ ⬈*[h] L2 →
                     G ⊢ ⬈*[h, o, ⓕ{I}V.T] 𝐒⦃L2⦄.
#h #o #G #I #L1 #V #H @(rdsx_ind_lpxs … H) -L1
#L1 #HL1 #IHL1 #L2 #T #H @(rdsx_ind_lpxs … H) -L2
#L2 #HL2 #IHL2 #HL12 @rdsx_intro_lpxs
#L0 #HL20 lapply (lpxs_trans … HL12 … HL20)
#HL10 #H elim (lfdneq_inv_flat … H) -H [ -HL1 -IHL2 | -HL2 -IHL1 ]
[ #HnV elim (lfdeq_dec h o L1 L2 V)
  [ #HV @(IHL1 … HL10) -IHL1 -HL12 -HL10
    /3 width=5 by rdsx_lpxs_trans, lfdeq_canc_sn/ (**) (* full auto too slow: 47s *)
  | -HnV -HL10 /3 width=4 by rdsx_lpxs_trans/
  ]
| /3 width=3 by/
]
qed-.

(* Basic_2A1: uses: lsx_flat *)
lemma rdsx_flat (h) (o) (G):
                ∀I,L,V. G ⊢ ⬈*[h, o, V] 𝐒⦃L⦄ →
                ∀T. G ⊢ ⬈*[h, o, T] 𝐒⦃L⦄ → G ⊢ ⬈*[h, o, ⓕ{I}V.T] 𝐒⦃L⦄.
/2 width=3 by rdsx_flat_lpxs/ qed.

fact rdsx_bind_lpxs_void_aux (h) (o) (G):
                             ∀p,I,L1,V. G ⊢ ⬈*[h, o, V] 𝐒⦃L1⦄ →
                             ∀Y,T. G ⊢ ⬈*[h, o, T] 𝐒⦃Y⦄ →
                             ∀L2. Y = L2.ⓧ → ⦃G, L1⦄ ⊢ ⬈*[h] L2 →
                             G ⊢ ⬈*[h, o, ⓑ{p,I}V.T] 𝐒⦃L2⦄.
#h #o #G #p #I #L1 #V #H @(rdsx_ind_lpxs … H) -L1
#L1 #_ #IHL1 #Y #T #H @(rdsx_ind_lpxs … H) -Y
#Y #HY #IHY #L2 #H #HL12 destruct
@rdsx_intro_lpxs #L0 #HL20
lapply (lpxs_trans … HL12 … HL20) #HL10 #H
elim (lfdneq_inv_bind_void … H) -H [ -IHY | -HY -IHL1 -HL12 ]
[ #HnV elim (lfdeq_dec h o L1 L2 V)
  [ #HV @(IHL1 … HL10) -IHL1 -HL12 -HL10
    /3 width=6 by rdsx_lpxs_trans, lpxs_bind_refl_dx, lfdeq_canc_sn/ (**) (* full auto too slow *)
  | -HnV -HL10 /4 width=4 by rdsx_lpxs_trans, lpxs_bind_refl_dx/
  ]
| /3 width=4 by lpxs_bind_refl_dx/
]
qed-.

lemma rdsx_bind_void (h) (o) (G):
                     ∀p,I,L,V. G ⊢ ⬈*[h, o, V] 𝐒⦃L⦄ →
                     ∀T. G ⊢ ⬈*[h, o, T] 𝐒⦃L.ⓧ⦄ →
                     G ⊢ ⬈*[h, o, ⓑ{p,I}V.T] 𝐒⦃L⦄.
/2 width=3 by rdsx_bind_lpxs_void_aux/ qed.
