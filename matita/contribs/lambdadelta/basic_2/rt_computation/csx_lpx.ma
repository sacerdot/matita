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

include "basic_2/computation/cpxs_cpxs.ma".
include "basic_2/computation/csx_alt.ma".
include "basic_2/computation/csx_lift.ma".

(* CONTEXT-SENSITIVE EXTENDED STRONGLY NORMALIZING TERMS ********************)

(* Advanced properties ******************************************************)

lemma csx_lpx_conf: ∀h,o,G,L1,L2. ⦃G, L1⦄ ⊢ ➡[h, o] L2 →
                    ∀T. ⦃G, L1⦄ ⊢ ⬊*[h, o] T → ⦃G, L2⦄ ⊢ ⬊*[h, o] T.
#h #o #G #L1 #L2 #HL12 #T #H @(csx_ind_alt … H) -T
/4 width=3 by csx_intro, lpx_cpx_trans/
qed-.

lemma csx_abst: ∀h,o,a,G,L,W. ⦃G, L⦄ ⊢ ⬊*[h, o] W →
                ∀T. ⦃G, L.ⓛW⦄ ⊢ ⬊*[h, o] T → ⦃G, L⦄ ⊢ ⬊*[h, o] ⓛ{a}W.T.
#h #o #a #G #L #W #HW @(csx_ind … HW) -W #W #_ #IHW #T #HT @(csx_ind … HT) -T #T #HT #IHT
@csx_intro #X #H1 #H2
elim (cpx_inv_abst1 … H1) -H1
#W0 #T0 #HLW0 #HLT0 #H destruct
elim (eq_false_inv_tpair_sn … H2) -H2
[ -IHT #H lapply (csx_cpx_trans … HLT0) // -HT
  #HT0 lapply (csx_lpx_conf … (L.ⓛW0) … HT0) -HT0 /3 width=1 by lpx_pair/
| -IHW -HLW0 -HT * #H destruct /3 width=1 by/
]
qed.

lemma csx_abbr: ∀h,o,a,G,L,V. ⦃G, L⦄ ⊢ ⬊*[h, o] V →
                ∀T. ⦃G, L.ⓓV⦄ ⊢ ⬊*[h, o] T → ⦃G, L⦄ ⊢ ⬊*[h, o] ⓓ{a}V. T.
#h #o #a #G #L #V #HV elim HV -V #V #_ #IHV #T #HT @(csx_ind_alt … HT) -T #T #HT #IHT
@csx_intro #X #H1 #H2
elim (cpx_inv_abbr1 … H1) -H1 *
[ #V1 #T1 #HLV1 #HLT1 #H destruct
  elim (eq_false_inv_tpair_sn … H2) -H2
  [ /4 width=5 by csx_cpx_trans, csx_lpx_conf, lpx_pair/
  | -IHV -HLV1 * #H destruct /3 width=1 by cpx_cpxs/
  ]
| -IHV -IHT -H2
  /3 width=8 by csx_cpx_trans, csx_inv_lift, drop_drop/
]
qed.

fact csx_appl_beta_aux: ∀h,o,a,G,L,U1. ⦃G, L⦄ ⊢ ⬊*[h, o] U1 →
                        ∀V,W,T1. U1 = ⓓ{a}ⓝW.V.T1 → ⦃G, L⦄ ⊢ ⬊*[h, o] ⓐV.ⓛ{a}W.T1.
#h #o #a #G #L #X #H @(csx_ind … H) -X
#X #HT1 #IHT1 #V #W #T1 #H1 destruct
@csx_intro #X #H1 #H2
elim (cpx_inv_appl1 … H1) -H1 *
[ -HT1 #V0 #Y #HLV0 #H #H0 destruct
  elim (cpx_inv_abst1 … H) -H #W0 #T0 #HLW0 #HLT0 #H destruct
  @IHT1 -IHT1 [4: // | skip |3: #H destruct /2 width=1 by/ ] -H2
  lapply (lsubr_cpx_trans … HLT0 (L.ⓓⓝW.V) ?) -HLT0 /3 width=1 by cpx_bind, cpx_flat, lsubr_beta/
| -IHT1 -H2 #b #V0 #W0 #W2 #T0 #T2 #HLV0 #HLW02 #HLT02 #H1 #H3 destruct
  lapply (lsubr_cpx_trans … HLT02 (L.ⓓⓝW0.V) ?) -HLT02
  /4 width=5 by csx_cpx_trans, cpx_bind, cpx_flat, lsubr_beta/
| -HT1 -IHT1 -H2 #b #V0 #V1 #W0 #W1 #T0 #T3 #_ #_ #_ #_ #H destruct
]
qed-.

(* Basic_1: was just: sn3_beta *)
lemma csx_appl_beta: ∀h,o,a,G,L,V,W,T. ⦃G, L⦄ ⊢ ⬊*[h, o] ⓓ{a}ⓝW.V.T → ⦃G, L⦄ ⊢ ⬊*[h, o] ⓐV.ⓛ{a}W.T.
/2 width=3 by csx_appl_beta_aux/ qed.

fact csx_appl_theta_aux: ∀h,o,a,G,L,U. ⦃G, L⦄ ⊢ ⬊*[h, o] U → ∀V1,V2. ⬆[0, 1] V1 ≡ V2 →
                         ∀V,T. U = ⓓ{a}V.ⓐV2.T → ⦃G, L⦄ ⊢ ⬊*[h, o] ⓐV1.ⓓ{a}V.T.
#h #o #a #G #L #X #H @(csx_ind_alt … H) -X #X #HVT #IHVT #V1 #V2 #HV12 #V #T #H destruct
lapply (csx_fwd_pair_sn … HVT) #HV
lapply (csx_fwd_bind_dx … HVT) -HVT #HVT
@csx_intro #X #HL #H
elim (cpx_inv_appl1 … HL) -HL *
[ -HV #V0 #Y #HLV10 #HL #H0 destruct
  elim (cpx_inv_abbr1 … HL) -HL *
  [ #V3 #T3 #HV3 #HLT3 #H0 destruct
    elim (lift_total V0 0 1) #V4 #HV04
    elim (eq_term_dec (ⓓ{a}V.ⓐV2.T) (ⓓ{a}V3.ⓐV4.T3))
    [ -IHVT #H0 destruct
      elim (eq_false_inv_tpair_sn … H) -H
      [ -HLV10 -HV3 -HLT3 -HVT
        >(lift_inj … HV12 … HV04) -V4
        #H elim H //
      | * #_ #H elim H //
      ]
    | -H -HVT #H
      lapply (cpx_lift … HLV10 (L.ⓓV) (Ⓕ) … HV12 … HV04) -HLV10 -HV12 /2 width=1 by drop_drop/ #HV24
      @(IHVT … H … HV04) -IHVT /4 width=1 by cpx_cpxs, cpx_bind, cpx_flat/
    ]
  | -H -IHVT #T0 #HLT0 #HT0 #H0 destruct
    lapply (csx_cpx_trans … HVT (ⓐV2.T0) ?) /2 width=1 by cpx_flat/ -T #HVT0
    lapply (csx_inv_lift … L … (Ⓕ) … 1 HVT0 ? ? ?) -HVT0
    /3 width=5 by csx_cpx_trans, cpx_pair_sn, drop_drop, lift_flat/
  ]
| -HV -HV12 -HVT -IHVT -H #b #V0 #W0 #W1 #T0 #T1 #_ #_ #_ #H destruct
| -IHVT -H #b #V0 #V3 #W0 #W1 #T0 #T1 #HLV10 #HV03 #HLW01 #HLT01 #H1 #H2 destruct
  lapply (cpx_lift … HLV10 (L. ⓓW0) … HV12 … HV03) -HLV10 -HV12 -HV03 /2 width=2 by drop_drop/ #HLV23
  @csx_abbr /2 width=3 by csx_cpx_trans/ -HV
  @(csx_lpx_conf … (L.ⓓW0)) /2 width=1 by lpx_pair/ -W1
  /4 width=5 by csx_cpxs_trans, cpx_cpxs, cpx_flat/
]
qed-.

lemma csx_appl_theta: ∀h,o,a,V1,V2. ⬆[0, 1] V1 ≡ V2 →
                      ∀G,L,V,T. ⦃G, L⦄ ⊢ ⬊*[h, o] ⓓ{a}V.ⓐV2.T → ⦃G, L⦄ ⊢ ⬊*[h, o] ⓐV1.ⓓ{a}V.T.
/2 width=5 by csx_appl_theta_aux/ qed.
