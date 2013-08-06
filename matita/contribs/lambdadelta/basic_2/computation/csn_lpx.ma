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

include "basic_2/grammar/tstc_tstc.ma".
include "basic_2/computation/cpxs_cpxs.ma".
include "basic_2/computation/csn_alt.ma".
include "basic_2/computation/csn_lift.ma".

(* CONTEXT-SENSITIVE EXTENDED STRONGLY NORMALIZING TERMS ********************)

(* Advanced properties ******************************************************)

lemma csn_lpx_conf: ∀h,g,G,L1,L2. ⦃G, L1⦄ ⊢ ➡[h, g] L2 →
                    ∀T. ⦃G, L1⦄ ⊢ ⬊*[h, g] T → ⦃G, L2⦄ ⊢ ⬊*[h, g] T.
#h #g #G #L1 #L2 #HL12 #T #H @(csn_ind_alt … H) -T #T #_ #IHT
@csn_intro #T0 #HLT0 #HT0
@IHT /2 width=2/ -IHT -HT0 /2 width=3 by lpx_cpx_trans/
qed.

lemma csn_abst: ∀h,g,a,G,L,W. ⦃G, L⦄ ⊢ ⬊*[h, g] W →
                ∀T. ⦃G, L.ⓛW⦄ ⊢ ⬊*[h, g] T → ⦃G, L⦄ ⊢ ⬊*[h, g] ⓛ{a}W.T.
#h #g #a #G #L #W #HW @(csn_ind … HW) -W #W #_ #IHW #T #HT @(csn_ind … HT) -T #T #HT #IHT
@csn_intro #X #H1 #H2
elim (cpx_inv_abst1 … H1) -H1
#W0 #T0 #HLW0 #HLT0 #H destruct
elim (eq_false_inv_tpair_sn … H2) -H2
[ -IHT #H lapply (csn_cpx_trans … HLT0) // -HT 
  #HT0 lapply (csn_lpx_conf … (L.ⓛW0) … HT0) -HT0 /2 width=1/ /3 width=1/
| -IHW -HLW0 -HT * #H destruct /3 width=1/
]
qed.

lemma csn_abbr: ∀h,g,a,G,L,V. ⦃G, L⦄ ⊢ ⬊*[h, g] V →
                ∀T. ⦃G, L.ⓓV⦄ ⊢ ⬊*[h, g] T → ⦃G, L⦄ ⊢ ⬊*[h, g] ⓓ{a}V. T.
#h #g #a #G #L #V #HV elim HV -V #V #_ #IHV #T #HT @(csn_ind_alt … HT) -T #T #HT #IHT
@csn_intro #X #H1 #H2
elim (cpx_inv_abbr1 … H1) -H1 *
[ #V1 #T1 #HLV1 #HLT1 #H destruct
  elim (eq_false_inv_tpair_sn … H2) -H2
  [ #HV1 @IHV // /2 width=1/ -HV1
    @(csn_lpx_conf … (L.ⓓV)) /2 width=1/ -HLV1 /2 width=3 by csn_cpx_trans/
  | -IHV -HLV1 * #H destruct /3 width=1/
  ]
| -IHV -IHT -H2 #T0 #HLT0 #HT0
  lapply (csn_cpx_trans … HT … HLT0) -T #HLT0
  lapply (csn_inv_lift … HLT0 … HT0) -T0 /2 width=3/
]
qed.

fact csn_appl_beta_aux: ∀h,g,a,G,L,U1. ⦃G, L⦄ ⊢ ⬊*[h, g] U1 →
                        ∀V,W,T1. U1 = ⓓ{a}ⓝW.V.T1 → ⦃G, L⦄ ⊢ ⬊*[h, g] ⓐV.ⓛ{a}W.T1.
#h #g #a #G #L #X #H @(csn_ind … H) -X
#X #HT1 #IHT1 #V #W #T1 #H1 destruct
@csn_intro #X #H1 #H2
elim (cpx_inv_appl1 … H1) -H1 *
[ -HT1 #V0 #Y #HLV0 #H #H0 destruct
  elim (cpx_inv_abst1 … H) -H #W0 #T0 #HLW0 #HLT0 #H destruct
  @IHT1 -IHT1 [4: // | skip |3: #H destruct /2 width=1/ ] -H2
  lapply (lsubr_cpx_trans … HLT0 (L.ⓓⓝW.V) ?) -HLT0 [ /2 width=1/ ] /3 width=1/
| -IHT1 -H2 #b #V0 #W0 #W2 #T0 #T2 #HLV0 #HLW02 #HLT02 #H1 #H3 destruct
  lapply (lsubr_cpx_trans … HLT02 (L.ⓓⓝW0.V) ?) -HLT02 [ /2 width=1/ ] #HT02
  @(csn_cpx_trans … HT1) -HT1 /3 width=1/
| -HT1 -IHT1 -H2 #b #V0 #V1 #W0 #W1 #T0 #T3 #_ #_ #_ #_ #H destruct
]
qed-.

(* Basic_1: was just: sn3_beta *)
lemma csn_appl_beta: ∀h,g,a,G,L,V,W,T. ⦃G, L⦄ ⊢ ⬊*[h, g] ⓓ{a}ⓝW.V.T → ⦃G, L⦄ ⊢ ⬊*[h, g] ⓐV.ⓛ{a}W.T.
/2 width=3 by csn_appl_beta_aux/ qed.

fact csn_appl_theta_aux: ∀h,g,a,G,L,U. ⦃G, L⦄ ⊢ ⬊*[h, g] U → ∀V1,V2. ⇧[0, 1] V1 ≡ V2 →
                         ∀V,T. U = ⓓ{a}V.ⓐV2.T → ⦃G, L⦄ ⊢ ⬊*[h, g] ⓐV1.ⓓ{a}V.T.
#h #g #a #G #L #X #H @(csn_ind_alt … H) -X #X #HVT #IHVT #V1 #V2 #HV12 #V #T #H destruct
lapply (csn_fwd_pair_sn … HVT) #HV
lapply (csn_fwd_bind_dx … HVT) -HVT #HVT
@csn_intro #X #HL #H
elim (cpx_inv_appl1 … HL) -HL *
[ -HV #V0 #Y #HLV10 #HL #H0 destruct
  elim (cpx_inv_abbr1 … HL) -HL *
  [ #V3 #T3 #HV3 #HLT3 #H0 destruct
    elim (lift_total V0 0 1) #V4 #HV04
    elim (term_eq_dec (ⓓ{a}V.ⓐV2.T) (ⓓ{a}V3.ⓐV4.T3))
    [ -IHVT #H0 destruct
      elim (eq_false_inv_tpair_sn … H) -H
      [ -HLV10 -HV3 -HLT3 -HVT
        >(lift_inj … HV12 … HV04) -V4
        #H elim H //
      | * #_ #H elim H //
      ]
    | -H -HVT #H
      lapply (cpx_lift … HLV10 (L. ⓓV) … HV12 … HV04) -HLV10 -HV12 /2 width=1/ #HV24
      @(IHVT … H … HV04) -IHVT // -H -HV04 /4 width=1/
    ]
  | -H -IHVT #T0 #HLT0 #HT0 #H0 destruct
    lapply (csn_cpx_trans … HVT (ⓐV2.T0) ?) /2 width=1/ -T #HVT0
    lapply (csn_inv_lift … L … 1 HVT0 ? ? ?) -HVT0 [ /2 width=4/ |2,3: skip | /2 width=1/ ] -V2 -T0 #HVY
    @(csn_cpx_trans … HVY) /2 width=1/
  ]
| -HV -HV12 -HVT -IHVT -H #b #V0 #W0 #W1 #T0 #T1 #_ #_ #_ #H destruct
| -IHVT -H #b #V0 #V3 #W0 #W1 #T0 #T1 #HLV10 #HV03 #HLW01 #HLT01 #H1 #H2 destruct
  lapply (cpx_lift … HLV10 (L. ⓓW0) … HV12 … HV03) -HLV10 -HV12 -HV03 /2 width=1/ #HLV23
  @csn_abbr /2 width=3 by csn_cpx_trans/ -HV
  @(csn_lpx_conf … (L. ⓓW0)) /2 width=1/ -W1
  @(csn_cpxs_trans … HVT) -HVT /3 width=1/
]
qed-.

lemma csn_appl_theta: ∀h,g,a,V1,V2. ⇧[0, 1] V1 ≡ V2 →
                      ∀G,L,V,T. ⦃G, L⦄ ⊢ ⬊*[h, g] ⓓ{a}V.ⓐV2.T → ⦃G, L⦄ ⊢ ⬊*[h, g] ⓐV1.ⓓ{a}V.T.
/2 width=5 by csn_appl_theta_aux/ qed.

(* Basic_1: was just: sn3_appl_appl *)
lemma csn_appl_simple_tstc: ∀h,g,G,L,V. ⦃G, L⦄ ⊢ ⬊*[h, g] V → ∀T1. ⦃G, L⦄ ⊢ ⬊*[h, g] T1 →
                            (∀T2. ⦃G, L⦄ ⊢ T1 ➡*[h, g] T2 → (T1 ≃ T2 → ⊥) → ⦃G, L⦄ ⊢ ⬊*[h, g] ⓐV.T2) →
                            𝐒⦃T1⦄ → ⦃G, L⦄ ⊢ ⬊*[h, g] ⓐV.T1.
#h #g #G #L #V #H @(csn_ind … H) -V #V #_ #IHV #T1 #H @(csn_ind … H) -T1 #T1 #H1T1 #IHT1 #H2T1 #H3T1
@csn_intro #X #HL #H
elim (cpx_inv_appl1_simple … HL) -HL //
#V0 #T0 #HLV0 #HLT10 #H0 destruct
elim (eq_false_inv_tpair_sn … H) -H
[ -IHT1 #HV0
  @(csn_cpx_trans … (ⓐV0.T1)) /2 width=1/ -HLT10
  @IHV -IHV // -H1T1 -H3T1 /2 width=1/ -HV0
  #T2 #HLT12 #HT12
  @(csn_cpx_trans … (ⓐV.T2)) /2 width=1/ -HLV0
  @H2T1 -H2T1 // -HLT12 /2 width=1/
| -IHV -H1T1 -HLV0 * #H #H1T10 destruct
  elim (tstc_dec T1 T0) #H2T10
  [ @IHT1 -IHT1 // /2 width=1/ -H1T10 /2 width=3/ -H3T1
    #T2 #HLT02 #HT02
    @H2T1 -H2T1 /2 width=3/ -HLT10 -HLT02 /3 width=3/
  | -IHT1 -H3T1 -H1T10
    @H2T1 -H2T1 /2 width=1/
  ]
]
qed.
