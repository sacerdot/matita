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
include "basic_2/computation/cprs_cprs.ma".
include "basic_2/computation/csn_alt.ma".
include "basic_2/computation/csn_lift.ma".

(* CONTEXT-SENSITIVE STRONGLY NORMALIZING TERMS *****************************)

(* Advanced properties ******************************************************)

lemma csn_lpr_conf: ∀L1,L2. L1 ⊢ ➡ L2 → ∀T. L1 ⊢ ⬊* T → L2 ⊢ ⬊* T.
#L1 #L2 #HL12 #T #H @(csn_ind_alt … H) -T #T #_ #IHT
@csn_intro #T0 #HLT0 #HT0
@IHT /2 width=2/ -IHT -HT0 /2 width=3 by lpr_cpr_trans/
qed.

lemma csn_abbr: ∀a,L,V. L ⊢ ⬊* V → ∀T. L. ⓓV ⊢ ⬊* T → L ⊢ ⬊* ⓓ{a}V. T.
#a #L #V #HV elim HV -V #V #_ #IHV #T #HT @(csn_ind_alt … HT) -T #T #HT #IHT
@csn_intro #X #H1 #H2
elim (cpr_inv_abbr1 … H1) -H1 *
[ #V1 #T1 #HLV1 #HLT1 #H destruct
  elim (eq_false_inv_tpair_sn … H2) -H2
  [ #HV1 @IHV // /2 width=1/ -HV1
    @(csn_lpr_conf (L. ⓓV)) /2 width=1/ -HLV1 /2 width=3/
  | -IHV -HLV1 * #H destruct /3 width=1/
  ]
| -IHV -IHT -H2 #T0 #HLT0 #HT0
  lapply (csn_cpr_trans … HT … HLT0) -T #HLT0
  lapply (csn_inv_lift … HLT0 … HT0) -T0 /2 width=3/
]
qed.

fact csn_appl_beta_aux: ∀a,L,W. L ⊢ ⬊* W → ∀U. L ⊢ ⬊* U →
                        ∀V,T. U = ⓓ{a}V. T → L ⊢ ⬊* ⓐV. ⓛ{a}W. T.
#a #L #W #H elim H -W #W #_ #IHW #X #H @(csn_ind_alt … H) -X #X #HVT #IHVT #V #T #H destruct
lapply (csn_fwd_pair_sn … HVT) #HV
lapply (csn_fwd_bind_dx … HVT) #HT -HVT
@csn_intro #X #H #H2
elim (cpr_inv_appl1 … H) -H *
[ #V0 #Y #HLV0 #H #H0 destruct
  elim (cpr_fwd_abst1 … H Abbr V) -H #W0 #T0 #HLW0 #HLT0 #H destruct
  elim (eq_false_inv_beta … H2) -H2
  [ -IHVT #HW0 @IHW -IHW [1,5: // |3: skip ] -HLW0 /2 width=1/ -HW0
    @csn_abbr /2 width=3/ -HV
    @(csn_lpr_conf (L.ⓓV)) /2 width=1/ -V0 /2 width=3/
  | -IHW -HLW0 -HV -HT * #H #HVT0 destruct
    @(IHVT … HVT0) -IHVT -HVT0 // /3 width=1/
  ]
| -IHW -IHVT -H2 #b #V0 #W0 #T0 #T1 #HLV0 #HLT01 #H1 #H2 destruct
  lapply (cpr_lsubr_trans … HLT01 (L.ⓓV) ?) -HLT01 /2 width=1/ #HLT01
  @csn_abbr /2 width=3/ -HV
  @(csn_lpr_conf (L. ⓓV)) /2 width=1/ -V0 /2 width=3/
| -IHW -IHVT -HV -HT -H2 #b #V0 #V1 #W0 #W1 #T0 #T1 #_ #_ #_ #_ #H destruct
]
qed-.

(* Basic_1: was: sn3_beta *)
lemma csn_appl_beta: ∀a,L,W. L ⊢ ⬊* W → ∀V,T. L ⊢ ⬊* ⓓ{a}V. T →
                     L ⊢ ⬊* ⓐV. ⓛ{a}W. T.
/2 width=3 by csn_appl_beta_aux/ qed.

fact csn_appl_theta_aux: ∀a,L,U. L ⊢ ⬊* U → ∀V1,V2. ⇧[0, 1] V1 ≡ V2 →
                         ∀V,T. U = ⓓ{a}V. ⓐV2. T → L ⊢ ⬊* ⓐV1. ⓓ{a}V. T.
#a #L #X #H @(csn_ind_alt … H) -X #X #HVT #IHVT #V1 #V2 #HV12 #V #T #H destruct
lapply (csn_fwd_pair_sn … HVT) #HV
lapply (csn_fwd_bind_dx … HVT) -HVT #HVT
@csn_intro #X #HL #H
elim (cpr_inv_appl1 … HL) -HL *
[ -HV #V0 #Y #HLV10 #HL #H0 destruct
  elim (cpr_inv_abbr1 … HL) -HL *
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
      lapply (cpr_lift … HLV10 (L. ⓓV) … HV12 … HV04) -HLV10 -HV12 /2 width=1/ #HV24
      @(IHVT … H … HV04) -IHVT // -H -HV04 /4 width=1/
    ]
  | -H -IHVT #T0 #HLT0 #HT0 #H0 destruct
    lapply (csn_cpr_trans … HVT (ⓐV2.T0) ?) /2 width=1/ -T #HVT0
    lapply (csn_inv_lift L … 1 HVT0 ? ? ?) -HVT0 [ /2 width=4/ |2,3: skip | /2 width=1/ ] -V2 -T0 #HVY
    @(csn_cpr_trans … HVY) /2 width=1/
  ]
| -HV -HV12 -HVT -IHVT -H #b #V0 #W0 #T0 #T1 #_ #_ #H destruct
| -IHVT -H #b #V0 #V3 #W0 #W1 #T0 #T1 #HLV10 #HV03 #HLW01 #HLT01 #H1 #H2 destruct
  lapply (cpr_lift … HLV10 (L. ⓓW0) … HV12 … HV03) -HLV10 -HV12 -HV03 /2 width=1/ #HLV23
  @csn_abbr /2 width=3/ -HV
  @(csn_lpr_conf (L. ⓓW0)) /2 width=1/ -W1
  @(csn_cprs_trans … HVT) -HVT /3 width=1/
]
qed-.

lemma csn_appl_theta: ∀a,V1,V2. ⇧[0, 1] V1 ≡ V2 →
                      ∀L,V,T. L ⊢ ⬊* ⓓ{a}V. ⓐV2. T → L ⊢ ⬊* ⓐV1. ⓓ{a}V. T.
/2 width=5 by csn_appl_theta_aux/ qed.

(* Basic_1: was only: sn3_appl_appl *)
lemma csn_appl_simple_tstc: ∀L,V. L ⊢ ⬊* V → ∀T1.
                            L ⊢ ⬊* T1 →
                            (∀T2. L ⊢ T1 ➡* T2 → (T1 ≃ T2 → ⊥) → L ⊢ ⬊* ⓐV. T2) →
                            𝐒⦃T1⦄ → L ⊢ ⬊* ⓐV. T1.
#L #V #H @(csn_ind … H) -V #V #_ #IHV #T1 #H @(csn_ind … H) -T1 #T1 #H1T1 #IHT1 #H2T1 #H3T1
@csn_intro #X #HL #H
elim (cpr_inv_appl1_simple … HL ?) -HL //
#V0 #T0 #HLV0 #HLT10 #H0 destruct
elim (eq_false_inv_tpair_sn … H) -H
[ -IHT1 #HV0
  @(csn_cpr_trans … (ⓐV0.T1)) /2 width=1/ -HLT10
  @IHV -IHV // -H1T1 -H3T1 /2 width=1/ -HV0
  #T2 #HLT12 #HT12
  @(csn_cpr_trans … (ⓐV.T2)) /2 width=1/ -HLV0
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
