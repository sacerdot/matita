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

include "basic_2/rt_computation/lfpxs_lfdeq.ma".
include "basic_2/rt_computation/lfpxs_cpxs.ma".
include "basic_2/rt_computation/lfpxs_lfpxs.ma".
include "basic_2/rt_computation/lfsx_lfsx.ma".

(* STRONGLY NORMALIZING LOCAL ENV.S FOR UNCOUNTED PARALLEL RT-TRANSITION ****)

(* Properties with uncounted rt-computation on referred entries *************)

(* Basic_2A1: uses: lsx_intro_alt *)
lemma lfsx_intro_lfpxs: ∀h,o,G,L1,T.
                        (∀L2. ⦃G, L1⦄ ⊢ ⬈*[h, T] L2 → (L1 ≡[h, o, T] L2 → ⊥) → G ⊢ ⬈*[h, o, T] 𝐒⦃L2⦄) →
                        G ⊢ ⬈*[h, o, T] 𝐒⦃L1⦄.
/4 width=1 by lfpx_lfpxs, lfsx_intro/ qed-.

(* Basic_2A1: uses: lsx_lpxs_trans *)
lemma lfsx_lfpxs_trans: ∀h,o,G,L1,T. G ⊢ ⬈*[h, o, T] 𝐒⦃L1⦄ →
                        ∀L2. ⦃G, L1⦄ ⊢ ⬈*[h, T] L2 → G ⊢ ⬈*[h, o, T] 𝐒⦃L2⦄.
#h #o #G #L1 #T #HL1 #L2 #H @(lfpxs_ind_sn … H) -L2
/2 width=3 by lfsx_lfpx_trans/
qed-.

(* Eliminators with uncounted rt-computation on referred entries ************)

lemma lfsx_ind_lfpxs_lfdeq: ∀h,o,G,T. ∀R:predicate lenv.
                            (∀L1. G ⊢ ⬈*[h, o, T] 𝐒⦃L1⦄ →
                                  (∀L2. ⦃G, L1⦄ ⊢ ⬈*[h, T] L2 → (L1 ≡[h, o, T] L2 → ⊥) → R L2) →
                                  R L1
                            ) →
                            ∀L1. G ⊢ ⬈*[h, o, T] 𝐒⦃L1⦄  →
                            ∀L0. ⦃G, L1⦄ ⊢ ⬈*[h, T] L0 → ∀L2. L0 ≡[h, o, T] L2 → R L2.
#h #o #G #T #R #IH #L1 #H @(lfsx_ind … H) -L1
#L1 #HL1 #IH1 #L0 #HL10 #L2 #HL02
@IH -IH /3 width=3 by lfsx_lfpxs_trans, lfsx_lfdeq_trans/ -HL1 #K2 #HLK2 #HnLK2
lapply (lfdeq_lfdneq_trans … HL02 … HnLK2) -HnLK2 #H
elim (lfdeq_lfpxs_trans … HLK2 … HL02) -L2 #K0 #HLK0 #HK02
lapply (lfdneq_lfdeq_canc_dx … H … HK02) -H #HnLK0
elim (lfdeq_dec h o L1 L0 T) #H
[ lapply (lfdeq_lfdneq_trans … H … HnLK0) -H -HnLK0 #Hn10
  lapply (lfpxs_trans … HL10 … HLK0) -L0 #H10
  elim (lfpxs_lfdneq_inv_step_sn … H10 …  Hn10) -H10 -Hn10
  /3 width=8 by lfdeq_trans/
| elim (lfpxs_lfdneq_inv_step_sn … HL10 … H) -HL10 -H #L #K #HL1 #HnL1 #HLK #HKL0
  elim (lfdeq_lfpxs_trans … HLK0 … HKL0) -L0
  /3 width=8 by lfpxs_trans, lfdeq_trans/
]
qed-.

(* Basic_2A1: uses: lsx_ind_alt *)
lemma lfsx_ind_lfpxs: ∀h,o,G,T. ∀R:predicate lenv.
                      (∀L1. G ⊢ ⬈*[h, o, T] 𝐒⦃L1⦄ →
                            (∀L2. ⦃G, L1⦄ ⊢ ⬈*[h, T] L2 → (L1 ≡[h, o, T] L2 → ⊥) → R L2) →
                            R L1
                      ) →
                      ∀L. G ⊢ ⬈*[h, o, T] 𝐒⦃L⦄  → R L.
#h #o #G #T #R #IH #L #HL
@(lfsx_ind_lfpxs_lfdeq … IH … HL) -IH -HL // (**) (* full auto fails *)
qed-.

(* Advanced properties ******************************************************)

fact lfsx_bind_lfpxs_aux: ∀h,o,p,I,G,L1,V. G ⊢ ⬈*[h, o, V] 𝐒⦃L1⦄ →
                          ∀Y,T. G ⊢ ⬈*[h, o, T] 𝐒⦃Y⦄ →
                          ∀L2. Y = L2.ⓑ{I}V → ⦃G, L1⦄ ⊢ ⬈*[h, ⓑ{p,I}V.T] L2 →
                          G ⊢ ⬈*[h, o, ⓑ{p,I}V.T] 𝐒⦃L2⦄.
#h #o #p #I #G #L1 #V #H @(lfsx_ind_lfpxs … H) -L1
#L1 #_ #IHL1 #Y #T #H @(lfsx_ind_lfpxs … H) -Y
#Y #HY #IHY #L2 #H #HL12 destruct
@lfsx_intro_lfpxs #L0 #HL20
lapply (lfpxs_trans … HL12 … HL20) #HL10 #H
elim (lfdneq_inv_bind … H) -H [ -IHY | -HY -IHL1 -HL12 ]
[ #HnV elim (lfdeq_dec h o L1 L2 V)
  [ #HV @(IHL1 … L0) -IHL1 -HL12
    /3 width=4 by lfsx_lfpxs_trans, lfpxs_fwd_bind_dx, lfpxs_fwd_pair_sn, lfdeq_canc_sn/ (**) (* full auto too slow *)
  | -HnV -HL10 /4 width=4 by lfsx_lfpxs_trans, lfpxs_fwd_pair_sn/
  ]
| /3 width=4 by lfpxs_fwd_bind_dx/
]
qed-.

(* Basic_2A1: uses: lsx_bind *)
lemma lfsx_bind: ∀h,o,p,I,G,L,V. G ⊢ ⬈*[h, o, V] 𝐒⦃L⦄ →
                 ∀T. G ⊢ ⬈*[h, o, T] 𝐒⦃L.ⓑ{I}V⦄ →
                 G ⊢ ⬈*[h, o, ⓑ{p,I}V.T] 𝐒⦃L⦄.
/2 width=3 by lfsx_bind_lfpxs_aux/ qed.

(* Basic_2A1: uses: lsx_flat_lpxs *)
lemma lfsx_flat_lfpxs: ∀h,o,I,G,L1,V. G ⊢ ⬈*[h, o, V] 𝐒⦃L1⦄ →
                       ∀L2,T. G ⊢ ⬈*[h, o, T] 𝐒⦃L2⦄ → ⦃G, L1⦄ ⊢ ⬈*[h, ⓕ{I}V.T] L2 →
                       G ⊢ ⬈*[h, o, ⓕ{I}V.T] 𝐒⦃L2⦄.
#h #o #I #G #L1 #V #H @(lfsx_ind_lfpxs … H) -L1
#L1 #HL1 #IHL1 #L2 #T #H @(lfsx_ind_lfpxs … H) -L2
#L2 #HL2 #IHL2 #HL12 @lfsx_intro_lfpxs
#L0 #HL20 lapply (lfpxs_trans … HL12 … HL20)
#HL10 #H elim (lfdneq_inv_flat … H) -H [ -HL1 -IHL2 | -HL2 -IHL1 ]
[ #HnV elim (lfdeq_dec h o L1 L2 V)
  [ #HV @(IHL1 … L0) -IHL1 -HL12
    /3 width=5 by lfsx_lfpxs_trans, lfpxs_fwd_flat_dx, lfpxs_fwd_pair_sn, lfdeq_canc_sn/ (**) (* full auto too slow: 47s *)
  | -HnV -HL10 /4 width=4 by lfsx_lfpxs_trans, lfpxs_fwd_pair_sn/
  ]
| /3 width=3 by lfpxs_fwd_flat_dx/
]
qed-.

(* Basic_2A1: uses: lsx_flat *)
lemma lfsx_flat: ∀h,o,I,G,L,V. G ⊢ ⬈*[h, o, V] 𝐒⦃L⦄ →
                 ∀T. G ⊢ ⬈*[h, o, T] 𝐒⦃L⦄ → G ⊢ ⬈*[h, o, ⓕ{I}V.T] 𝐒⦃L⦄.
/2 width=3 by lfsx_flat_lfpxs/ qed.

fact lfsx_bind_lfpxs_void_aux: ∀h,o,p,I,G,L1,V. G ⊢ ⬈*[h, o, V] 𝐒⦃L1⦄ →
                               ∀Y,T. G ⊢ ⬈*[h, o, T] 𝐒⦃Y⦄ →
                               ∀L2. Y = L2.ⓧ → ⦃G, L1⦄ ⊢ ⬈*[h, ⓑ{p,I}V.T] L2 →
                               G ⊢ ⬈*[h, o, ⓑ{p,I}V.T] 𝐒⦃L2⦄.
#h #o #p #I #G #L1 #V #H @(lfsx_ind_lfpxs … H) -L1
#L1 #_ #IHL1 #Y #T #H @(lfsx_ind_lfpxs … H) -Y
#Y #HY #IHY #L2 #H #HL12 destruct
@lfsx_intro_lfpxs #L0 #HL20
lapply (lfpxs_trans … HL12 … HL20) #HL10 #H
elim (lfdneq_inv_bind_void … H) -H [ -IHY | -HY -IHL1 -HL12 ]
[ #HnV elim (lfdeq_dec h o L1 L2 V)
  [ #HV @(IHL1 … L0) -IHL1 -HL12
    /3 width=6 by lfsx_lfpxs_trans, lfpxs_fwd_bind_dx_void, lfpxs_fwd_pair_sn, lfdeq_canc_sn/ (**) (* full auto too slow *)
  | -HnV -HL10 /4 width=4 by lfsx_lfpxs_trans, lfpxs_fwd_pair_sn/
  ]
| /3 width=4 by lfpxs_fwd_bind_dx_void/
]
qed-.

lemma lfsx_bind_void: ∀h,o,p,I,G,L,V. G ⊢ ⬈*[h, o, V] 𝐒⦃L⦄ →
                      ∀T. G ⊢ ⬈*[h, o, T] 𝐒⦃L.ⓧ⦄ →
                      G ⊢ ⬈*[h, o, ⓑ{p,I}V.T] 𝐒⦃L⦄.
/2 width=3 by lfsx_bind_lfpxs_void_aux/ qed.
