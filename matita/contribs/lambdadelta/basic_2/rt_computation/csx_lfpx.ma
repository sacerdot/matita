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

include "basic_2/rt_computation/cpxs_lfpx.ma".
include "basic_2/rt_computation/csx_cpxs.ma".

(* STRONGLY NORMALIZING TERMS FOR UNCOUNTED PARALLEL RT-TRANSITION **********)

(* Properties with uncounted parallel rt-transition on referred entries *****)

(* Basic_2A1: was just: csx_lpx_conf *)
lemma csx_lfpx_conf: ∀h,o,G,L1,T. ⦃G, L1⦄ ⊢ ⬈*[h, o] 𝐒⦃T⦄ →
                     ∀L2. ⦃G, L1⦄ ⊢ ⬈[h, T] L2 → ⦃G, L2⦄ ⊢ ⬈*[h, o] 𝐒⦃T⦄.
#h #o #G #L1 #T #H @(csx_ind_cpxs … H) -T
/5 width=3 by csx_intro, lfpx_cpx_trans, lfpx_cpxs_conf/
qed-.

(* Advanced properties ******************************************************)

lemma csx_abst: ∀h,o,p,G,L,W. ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃W⦄ →
                ∀T. ⦃G, L.ⓛW⦄ ⊢ ⬈*[h, o] 𝐒⦃T⦄ → ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃ⓛ{p}W.T⦄.
#h #o #p #G #L #W #HW @(csx_ind … HW) -W
#W #_ #IHW #T #HT @(csx_ind … HT) -T #T #HT #IHT
@csx_intro #X #H1 #H2
elim (cpx_inv_abst1 … H1) -H1
#W0 #T0 #HLW0 #HLT0 #H destruct
elim (tdneq_inv_pair … H2) -H2
[ #H elim H -H //
| -IHT #H lapply (csx_cpx_trans … o … HLT0) // -HT
  #HT0 lapply (csx_lfpx_conf … HT0 … (L.ⓛW0)) -HT0 /4 width=1 by lfpx_pair_refl/
| -IHW -HT /4 width=3 by csx_cpx_trans, cpx_pair_sn/
]
qed.

lemma csx_abbr: ∀h,o,p,G,L,V. ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃V⦄ →
                ∀T. ⦃G, L.ⓓV⦄ ⊢ ⬈*[h, o] 𝐒⦃T⦄ → ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃ⓓ{p}V.T⦄.
#h #o #p #G #L #V #HV @(csx_ind … HV) -V
#V #_ #IHV #T #HT @(csx_ind_cpxs … HT) -T #T #HT #IHT
@csx_intro #X #H1 #H2
elim (cpx_inv_abbr1 … H1) -H1 *
[ #V1 #T1 #HLV1 #HLT1 #H destruct
  elim (tdneq_inv_pair … H2) -H2
  [ #H elim H -H //
  | /4 width=3 by csx_cpx_trans, csx_lfpx_conf, lfpx_pair_refl/
  | -IHV /4 width=3 by csx_cpx_trans, cpx_cpxs, cpx_pair_sn/
  ]
| -IHV -IHT -H2
  /4 width=7 by csx_cpx_trans, csx_inv_lifts, drops_drop, drops_refl/
]
qed.

fact csx_appl_theta_aux: ∀h,o,p,G,L,U. ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃U⦄ → ∀V1,V2. ⬆*[1] V1 ≘ V2 →
                         ∀V,T. U = ⓓ{p}V.ⓐV2.T → ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃ⓐV1.ⓓ{p}V.T⦄.
#h #o #p #G #L #X #H @(csx_ind_cpxs … H) -X
#X #HVT #IHVT #V1 #V2 #HV12 #V #T #H destruct
lapply (csx_fwd_pair_sn … HVT) #HV
lapply (csx_fwd_bind_dx … HVT) -HVT #HVT
@csx_intro #X #HL #H
elim (cpx_inv_appl1 … HL) -HL *
[ -HV #V0 #Y #HLV10 #HL #H0 destruct
  elim (cpx_inv_abbr1 … HL) -HL *
  [ -HVT #V3 #T3 #HV3 #HLT3 #H0 destruct
    elim (cpx_lifts_sn … HLV10 (Ⓣ) … (L.ⓓV) … HV12) -HLV10 /3 width=1 by drops_refl, drops_drop/ #V4 #HV04 #HV24
    elim (tdeq_dec h o (ⓓ{p}V.ⓐV2.T) (ⓓ{p}V3.ⓐV4.T3)) #H0
    [ -IHVT -HV3 -HV24 -HLT3
      elim (tdeq_inv_pair … H0) -H0 #_ #HV3 #H0
      elim (tdeq_inv_pair … H0) -H0 #_ #HV24 #HT3
      elim (tdneq_inv_pair … H) -H #H elim H -H -G -L
      /3 width=6 by tdeq_inv_lifts_bi, tdeq_pair/
    | -V1 @(IHVT … H0 … HV04) -o -V0 /4 width=1 by cpx_cpxs, cpx_flat, cpx_bind/
    ]
  | -H -IHVT #T0 #HLT0 #HT0 #H0 destruct
    lapply (csx_cpx_trans … HVT (ⓐV2.T0) ?) /2 width=1 by cpx_flat/ -T #HVT0
    lapply (csx_inv_lifts … HVT0 (Ⓣ) … L ???) -HVT0
    /3 width=5 by csx_cpx_trans, cpx_pair_sn, drops_refl, drops_drop, lifts_flat/
  ]
| -HV -HV12 -HVT -IHVT -H #b #V0 #W0 #W1 #T0 #T1 #_ #_ #_ #H destruct
| -IHVT -H #b #V0 #V3 #W0 #W1 #T0 #T1 #HLV10 #HV03 #HLW01 #HLT01 #H1 #H2 destruct
  lapply (cpx_lifts_bi … HLV10 (Ⓣ) … (L.ⓓW0) … HV12 … HV03) -HLV10 -HV12 -HV03 /3 width=1 by drops_refl, drops_drop/ #HLV23
  @csx_abbr /2 width=3 by csx_cpx_trans/ -HV
  @(csx_lfpx_conf … (L.ⓓW0)) /2 width=1 by lfpx_pair_refl/ -W1
  /4 width=5 by csx_cpxs_trans, cpx_cpxs, cpx_flat/
]
qed-.

lemma csx_appl_theta: ∀h,o,p,G,L,V,V2,T. ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃ⓓ{p}V.ⓐV2.T⦄ →
                      ∀V1. ⬆*[1] V1 ≘ V2 → ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃ⓐV1.ⓓ{p}V.T⦄.
/2 width=5 by csx_appl_theta_aux/ qed.
