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

include "basic_2/grammar/tstc_vector.ma".
include "basic_2/substitution/lift_vector.ma".
include "basic_2/computation/cprs_tstc.ma".

(* CONTEXT-SENSITIVE PARALLEL COMPUTATION ON TERMS **************************)

(* Vector form of forward lemmas involving same top term constructor ********)

(* Basic_1: was just: nf2_iso_appls_lref *)
lemma cprs_fwd_cnf_vector: ∀L,T.  𝐒⦃T⦄ → L ⊢ 𝐍⦃T⦄ → ∀Vs,U. L ⊢ ⒶVs.T ➡* U → ⒶVs.T ≃ U.
#L #T #H1T #H2T #Vs elim Vs -Vs [ @(cprs_fwd_cnf … H2T) ] (**) (* /2 width=3 by cprs_fwd_cnf/ does not work *)
#V #Vs #IHVs #U #H
elim (cprs_inv_appl1 … H) -H *
[ -IHVs #V0 #T0 #_ #_ #H destruct /2 width=1/
| #a #V0 #W0 #T0 #HV0 #HT0 #HU
  lapply (IHVs … HT0) -IHVs -HT0 #HT0
  elim (tstc_inv_bind_appls_simple … HT0 ?) //
| #a #V1 #V2 #V0 #T0 #HV1 #HV12 #HT0 #HU
  lapply (IHVs … HT0) -IHVs -HT0 #HT0
  elim (tstc_inv_bind_appls_simple … HT0 ?) //
]
qed-.

(* Basic_1: was: pr3_iso_appls_beta *)
lemma cprs_fwd_beta_vector: ∀a,L,Vs,V,W,T,U. L ⊢ ⒶVs. ⓐV. ⓛ{a}W. T ➡* U →
                            ⒶVs. ⓐV. ⓛ{a}W. T ≃ U ∨ L ⊢ ⒶVs. ⓓ{a}V. T ➡* U.
#a #L #Vs elim Vs -Vs /2 width=1 by cprs_fwd_beta/
#V0 #Vs #IHVs #V #W #T #U #H
elim (cprs_inv_appl1 … H) -H *
[ -IHVs #V1 #T1 #_ #_ #H destruct /2 width=1/
| #b #V1 #W1 #T1 #HV01 #HT1 #HU
  elim (IHVs … HT1) -IHVs -HT1 #HT1
  [ elim (tstc_inv_bind_appls_simple … HT1 ?) //
  | @or_intror -W (**) (* explicit constructor *)
    @(cprs_trans … HU) -U
    @(cprs_strap1 … (ⓐV1.ⓛ{b}W1.T1)) [ /2 width=1/ ] -V -V0 -Vs -T /3 width=1/
  ]
| #b #V1 #V2 #V3 #T1 #HV01 #HV12 #HT1 #HU
  elim (IHVs … HT1) -IHVs -HT1 #HT1
  [ elim (tstc_inv_bind_appls_simple … HT1 ?) //
  | @or_intror -W (**) (* explicit constructor *)
    @(cprs_trans … HU) -U
    @(cprs_strap1 … (ⓐV1.ⓓ{b}V3.T1)) [ /2 width=1/ ] -V -V0 -Vs -T /3 width=3/
  ]
]
qed-.

lemma cprs_fwd_delta_vector: ∀L,K,V1,i. ⇩[0, i] L ≡ K. ⓓV1 →
                             ∀V2. ⇧[0, i + 1] V1 ≡ V2 →
                             ∀Vs,U. L ⊢ ⒶVs.#i ➡* U →
                             ⒶVs.#i ≃ U ∨ L ⊢ ⒶVs.V2 ➡* U.
#L #K #V1 #i #HLK #V2 #HV12 #Vs elim Vs -Vs /2 width=4 by cprs_fwd_delta/
#V #Vs #IHVs #U #H -K -V1
elim (cprs_inv_appl1 … H) -H *
[ -IHVs #V0 #T0 #_ #_ #H destruct /2 width=1/
| #b #V0 #W0 #T0 #HV0 #HT0 #HU
  elim (IHVs … HT0) -IHVs -HT0 #HT0
  [ elim (tstc_inv_bind_appls_simple … HT0 ?) //
  | @or_intror -i (**) (* explicit constructor *)
    @(cprs_trans … HU) -U
    @(cprs_strap1 … (ⓐV0.ⓛ{b}W0.T0)) [ /2 width=1/ ] -V -V2 -Vs /3 width=1/
  ]
| #b #V0 #V1 #V3 #T0 #HV0 #HV01 #HT0 #HU
  elim (IHVs … HT0) -IHVs -HT0 #HT0
  [ elim (tstc_inv_bind_appls_simple … HT0 ?) //
  | @or_intror -i (**) (* explicit constructor *)
    @(cprs_trans … HU) -U
    @(cprs_strap1 … (ⓐV0.ⓓ{b}V3.T0)) [ /2 width=1/ ] -V -V2 -Vs /3 width=3/
  ]
]
qed-.

(* Basic_1: was: pr3_iso_appls_abbr *)
lemma cprs_fwd_theta_vector: ∀L,V1s,V2s. ⇧[0, 1] V1s ≡ V2s →
                             ∀a,V,T,U. L ⊢ ⒶV1s. ⓓ{a}V. T ➡* U →
                             ⒶV1s. ⓓ{a}V. T ≃ U ∨ L ⊢ ⓓ{a}V. ⒶV2s. T ➡* U.
#L #V1s #V2s * -V1s -V2s /3 width=1/
#V1s #V2s #V1a #V2a #HV12a #HV12s #a
generalize in match HV12a; -HV12a
generalize in match V2a; -V2a
generalize in match V1a; -V1a
elim HV12s -V1s -V2s /2 width=1 by cprs_fwd_theta/
#V1s #V2s #V1b #V2b #HV12b #_ #IHV12s #V1a #V2a #HV12a #V #T #U #H
elim (cprs_inv_appl1 … H) -H *
[ -IHV12s -HV12a -HV12b #V0 #T0 #_ #_ #H destruct /2 width=1/
| #b #V0a #W0 #T0 #HV10a #HT0 #HU
  elim (IHV12s … HV12b … HT0) -IHV12s -HT0 #HT0
  [ -HV12a -HV12b -HV10a -HU
    elim (tstc_inv_pair1 … HT0) #V1 #T1 #H destruct
  | @or_intror -V1s (**) (* explicit constructor *)
    @(cprs_trans … HU) -U
    elim (cprs_inv_abbr1 … HT0) -HT0 *
    [ -HV12a -HV12b -HV10a #V1 #T1 #_ #_ #H destruct
    | -V1b #X #HT1 #H #H0 destruct
      elim (lift_inv_bind1 … H) -H #W1 #T1 #HW01 #HT01 #H destruct
      @(cprs_trans … (+ⓓV.ⓐV2a.ⓛ{b}W1.T1)) [ /3 width=1/ ] -T -V2b -V2s
      @(cprs_strap2 … (ⓐV1a.ⓛ{b}W0.T0)) [ /5 width=7/ ] -V -V2a -W1 -T1
      @(cprs_strap2 … (ⓓ{b}V1a.T0)) [ /3 width=1/ ] -W0 /2 width=1/
    ]
  ]
| #b #V0a #Va #V0 #T0 #HV10a #HV0a #HT0 #HU
  elim (IHV12s … HV12b … HT0) -HV12b -IHV12s -HT0 #HT0
  [ -HV12a -HV10a -HV0a -HU
    elim (tstc_inv_pair1 … HT0) #V1 #T1 #H destruct
  | @or_intror -V1s -V1b (**) (* explicit constructor *)
    @(cprs_trans … HU) -U
    elim (cprs_inv_abbr1 … HT0) -HT0 *
    [ #V1 #T1 #HV1 #HT1 #H destruct
      lapply (cprs_lift (L.ⓓV) … HV12a … HV10a … HV0a) -V1a -V0a [ /2 width=1/ ] #HV2a
      @(cprs_trans … (ⓓ{a}V.ⓐV2a.T1)) [ /3 width=1/ ] -T -V2b -V2s /3 width=1/
    | #X #HT1 #H #H0 destruct
      elim (lift_inv_bind1 … H) -H #V1 #T1 #HW01 #HT01 #H destruct
      lapply (cprs_lift (L.ⓓV0) … HV12a … HV10a … HV0a) -V0a [ /2 width=1/ ] #HV2a
      @(cprs_trans … (+ⓓV.ⓐV2a.ⓓ{b}V1.T1)) [ /3 width=1/ ] -T -V2b -V2s
      @(cprs_strap2 … (ⓐV1a.ⓓ{b}V0.T0)) [ /5 width=7/ ] -V -V1 -T1
      @(cprs_strap2 … (ⓓ{b}V0.ⓐV2a.T0)) [ /3 width=3/ ] -V1a /3 width=1/
    ]
  ]
]  
qed-.

(* Basic_1: was: pr3_iso_appls_cast *)
lemma cprs_fwd_tau_vector: ∀L,Vs,W,T,U. L ⊢ ⒶVs. ⓝW. T ➡* U →
                           ⒶVs. ⓝW. T ≃ U ∨ L ⊢ ⒶVs. T ➡* U.
#L #Vs elim Vs -Vs /2 width=1 by cprs_fwd_tau/
#V #Vs #IHVs #W #T #U #H
elim (cprs_inv_appl1 … H) -H *
[ -IHVs #V0 #T0 #_ #_ #H destruct /2 width=1/
| #b #V0 #W0 #T0 #HV0 #HT0 #HU
  elim (IHVs … HT0) -IHVs -HT0 #HT0
  [ elim (tstc_inv_bind_appls_simple … HT0 ?) //
  | @or_intror -W (**) (* explicit constructor *)
    @(cprs_trans … HU) -U
    @(cprs_strap1 … (ⓐV0.ⓛ{b}W0.T0)) [ /2 width=1/ ] -V -Vs -T /3 width=1/
  ]
| #b #V0 #V1 #V2 #T0 #HV0 #HV01 #HT0 #HU
  elim (IHVs … HT0) -IHVs -HT0 #HT0
  [ elim (tstc_inv_bind_appls_simple … HT0 ?) //
  | @or_intror -W (**) (* explicit constructor *)
    @(cprs_trans … HU) -U
    @(cprs_strap1 … (ⓐV0.ⓓ{b}V2.T0)) [ /2 width=1/ ] -V -Vs -T /3 width=3/
]
qed-.
