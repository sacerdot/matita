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
include "basic_2/relocation/lift_vector.ma".
include "basic_2/computation/cpxs_tstc.ma".

(* CONTEXT-SENSITIVE EXTENDED PARALLEL COMPUTATION ON TERMS *****************)

(* Vector form of forward lemmas involving same top term constructor ********)

(* Basic_1: was just: nf2_iso_appls_lref *)
lemma cpxs_fwd_cnx_vector: ∀h,g,G,L,T.  𝐒⦃T⦄ → ⦃G, L⦄ ⊢ 𝐍[h, g]⦃T⦄ →
                           ∀Vs,U. ⦃G, L⦄ ⊢ ⒶVs.T ➡*[h, g] U → ⒶVs.T ≃ U.
#h #g #G #L #T #H1T #H2T #Vs elim Vs -Vs [ @(cpxs_fwd_cnx … H2T) ] (**) (* /2 width=3 by cpxs_fwd_cnx/ does not work *)
#V #Vs #IHVs #U #H
elim (cpxs_inv_appl1 … H) -H *
[ -IHVs #V0 #T0 #_ #_ #H destruct /2 width=1/
| #a #W0 #T0 #HT0 #HU
  lapply (IHVs … HT0) -IHVs -HT0 #HT0
  elim (tstc_inv_bind_appls_simple … HT0) //
| #a #V1 #V2 #V0 #T0 #HV1 #HV12 #HT0 #HU
  lapply (IHVs … HT0) -IHVs -HT0 #HT0
  elim (tstc_inv_bind_appls_simple … HT0) //
]
qed-.

lemma cpxs_fwd_sort_vector: ∀h,g,G,L,k,Vs,U. ⦃G, L⦄ ⊢ ⒶVs.⋆k ➡*[h, g] U →
                            ⒶVs.⋆k ≃ U ∨ ⦃G, L⦄ ⊢ ⒶVs.⋆(next h k) ➡*[h, g] U.
#h #g #G #L #k #Vs elim Vs -Vs /2 width=1 by cpxs_fwd_sort/
#V #Vs #IHVs #U #H
elim (cpxs_inv_appl1 … H) -H *
[ -IHVs #V1 #T1 #_ #_ #H destruct /2 width=1/
| #a #W1 #T1 #HT1 #HU
  elim (IHVs … HT1) -IHVs -HT1 #HT1
  [ elim (tstc_inv_bind_appls_simple … HT1) //
  | @or_intror (**) (* explicit constructor *)
    @(cpxs_trans … HU) -U
    @(cpxs_strap1 … (ⓐV.ⓛ{a}W1.T1)) [ /2 width=1/ ] -Vs /3 width=1/
  ]
| #a #V1 #V2 #V3 #T1 #HV01 #HV12 #HT1 #HU
  elim (IHVs … HT1) -IHVs -HT1 #HT1
  [ elim (tstc_inv_bind_appls_simple … HT1) //
  | @or_intror (**) (* explicit constructor *)
    @(cpxs_trans … HU) -U
    @(cpxs_strap1 … (ⓐV1.ⓓ{a}V3.T1)) [ /2 width=1/ ] -Vs /3 width=3/
  ]
]
qed-.


(* Basic_1: was just: pr3_iso_appls_beta *)
lemma cpxs_fwd_beta_vector: ∀h,g,a,G,L,Vs,V,W,T,U. ⦃G, L⦄ ⊢ ⒶVs.ⓐV.ⓛ{a}W.T ➡*[h, g] U →
                            ⒶVs. ⓐV. ⓛ{a}W. T ≃ U ∨ ⦃G, L⦄ ⊢ ⒶVs.ⓓ{a}ⓝW.V.T ➡*[h, g] U.
#h #g #a #G #L #Vs elim Vs -Vs /2 width=1 by cpxs_fwd_beta/
#V0 #Vs #IHVs #V #W #T #U #H
elim (cpxs_inv_appl1 … H) -H *
[ -IHVs #V1 #T1 #_ #_ #H destruct /2 width=1/
| #b #W1 #T1 #HT1 #HU
  elim (IHVs … HT1) -IHVs -HT1 #HT1
  [ elim (tstc_inv_bind_appls_simple … HT1) //
  | @or_intror (**) (* explicit constructor *)
    @(cpxs_trans … HU) -U
    @(cpxs_strap1 … (ⓐV0.ⓛ{b}W1.T1)) [ /2 width=1/ ] -V -Vs -T /3 width=1/
  ]
| #b #V1 #V2 #V3 #T1 #HV01 #HV12 #HT1 #HU
  elim (IHVs … HT1) -IHVs -HT1 #HT1
  [ elim (tstc_inv_bind_appls_simple … HT1) //
  | @or_intror (**) (* explicit constructor *)
    @(cpxs_trans … HU) -U
    @(cpxs_strap1 … (ⓐV1.ⓓ{b}V3.T1)) [ /2 width=1/ ] -V -V0 -Vs -T /3 width=3/
  ]
]
qed-.

lemma cpxs_fwd_delta_vector: ∀h,g,I,G,L,K,V1,i. ⇩[0, i] L ≡ K.ⓑ{I}V1 →
                             ∀V2. ⇧[0, i + 1] V1 ≡ V2 →
                             ∀Vs,U. ⦃G, L⦄ ⊢ ⒶVs.#i ➡*[h, g] U →
                             ⒶVs.#i ≃ U ∨ ⦃G, L⦄ ⊢ ⒶVs.V2 ➡*[h, g] U.
#h #g #I #G #L #K #V1 #i #HLK #V2 #HV12 #Vs elim Vs -Vs /2 width=5 by cpxs_fwd_delta/
#V #Vs #IHVs #U #H -K -V1
elim (cpxs_inv_appl1 … H) -H *
[ -IHVs #V0 #T0 #_ #_ #H destruct /2 width=1/
| #b #W0 #T0 #HT0 #HU
  elim (IHVs … HT0) -IHVs -HT0 #HT0
  [ elim (tstc_inv_bind_appls_simple … HT0) //
  | @or_intror -i (**) (* explicit constructor *)
    @(cpxs_trans … HU) -U
    @(cpxs_strap1 … (ⓐV.ⓛ{b}W0.T0)) [ /2 width=1/ ] -V2 -Vs /3 width=1/
  ]
| #b #V0 #V1 #V3 #T0 #HV0 #HV01 #HT0 #HU
  elim (IHVs … HT0) -IHVs -HT0 #HT0
  [ elim (tstc_inv_bind_appls_simple … HT0) //
  | @or_intror -i (**) (* explicit constructor *)
    @(cpxs_trans … HU) -U
    @(cpxs_strap1 … (ⓐV0.ⓓ{b}V3.T0)) [ /2 width=1/ ] -V -V2 -Vs /3 width=3/
  ]
]
qed-.

(* Basic_1: was just: pr3_iso_appls_abbr *)
lemma cpxs_fwd_theta_vector: ∀h,g,G,L,V1s,V2s. ⇧[0, 1] V1s ≡ V2s →
                             ∀a,V,T,U. ⦃G, L⦄ ⊢ ⒶV1s.ⓓ{a}V.T ➡*[h, g] U →
                             ⒶV1s. ⓓ{a}V. T ≃ U ∨ ⦃G, L⦄ ⊢ ⓓ{a}V.ⒶV2s.T ➡*[h, g] U.
#h #g #G #L #V1s #V2s * -V1s -V2s /3 width=1/
#V1s #V2s #V1a #V2a #HV12a #HV12s #a
generalize in match HV12a; -HV12a
generalize in match V2a; -V2a
generalize in match V1a; -V1a
elim HV12s -V1s -V2s /2 width=1 by cpxs_fwd_theta/
#V1s #V2s #V1b #V2b #HV12b #_ #IHV12s #V1a #V2a #HV12a #V #T #U #H
elim (cpxs_inv_appl1 … H) -H *
[ -IHV12s -HV12a -HV12b #V0 #T0 #_ #_ #H destruct /2 width=1/
| #b #W0 #T0 #HT0 #HU
  elim (IHV12s … HV12b … HT0) -IHV12s -HT0 #HT0
  [ -HV12a -HV12b -HU
    elim (tstc_inv_pair1 … HT0) #V1 #T1 #H destruct
  | @or_intror -V1s (**) (* explicit constructor *)
    @(cpxs_trans … HU) -U
    elim (cpxs_inv_abbr1 … HT0) -HT0 *
    [ -HV12a -HV12b #V1 #T1 #_ #_ #H destruct
    | -V1b #X #HT1 #H #H0 destruct
      elim (lift_inv_bind1 … H) -H #W1 #T1 #HW01 #HT01 #H destruct
      @(cpxs_trans … (+ⓓV.ⓐV2a.ⓛ{b}W1.T1)) [ /3 width=1/ ] -T -V2b -V2s
      @(cpxs_strap2 … (ⓐV1a.ⓛ{b}W0.T0)) [2: /2 width=1/ ]
      /4 width=7 by cpx_zeta, lift_bind, lift_flat/ (* auto too slow without trace *)
    ]
  ]
| #b #V0a #Va #V0 #T0 #HV10a #HV0a #HT0 #HU
  elim (IHV12s … HV12b … HT0) -HV12b -IHV12s -HT0 #HT0
  [ -HV12a -HV10a -HV0a -HU
    elim (tstc_inv_pair1 … HT0) #V1 #T1 #H destruct
  | @or_intror -V1s -V1b (**) (* explicit constructor *)
    @(cpxs_trans … HU) -U
    elim (cpxs_inv_abbr1 … HT0) -HT0 *
    [ #V1 #T1 #HV1 #HT1 #H destruct
      lapply (cpxs_lift … HV10a (L.ⓓV) … HV12a … HV0a) -V1a -V0a [ /2 width=1/ ] #HV2a
      @(cpxs_trans … (ⓓ{a}V.ⓐV2a.T1)) [ /3 width=1/ ] -T -V2b -V2s /3 width=1/
    | #X #HT1 #H #H0 destruct
      elim (lift_inv_bind1 … H) -H #V1 #T1 #HW01 #HT01 #H destruct
      lapply (cpxs_lift … HV10a (L.ⓓV0) … HV12a … HV0a) -V0a [ /2 width=1/ ] #HV2a
      @(cpxs_trans … (+ⓓV.ⓐV2a.ⓓ{b}V1.T1)) [ /3 width=1/ ] -T -V2b -V2s
      @(cpxs_strap2 … (ⓐV1a.ⓓ{b}V0.T0)) [ /4 width=7 by cpx_zeta, lift_bind, lift_flat/ ] -V -V1 -T1 (* auto too slow without trace *)
      @(cpxs_strap2 … (ⓓ{b}V0.ⓐV2a.T0)) [ /3 width=3/ ] -V1a /3 width=1/
    ]
  ]
]
qed-.

(* Basic_1: was just: pr3_iso_appls_cast *)
lemma cpxs_fwd_cast_vector: ∀h,g,G,L,Vs,W,T,U. ⦃G, L⦄ ⊢ ⒶVs.ⓝW.T ➡*[h, g] U →
                            ∨∨ ⒶVs. ⓝW. T ≃ U
                             | ⦃G, L⦄ ⊢ ⒶVs.T ➡*[h, g] U
                             | ⦃G, L⦄ ⊢ ⒶVs.W ➡*[h, g] U.
#h #g #G #L #Vs elim Vs -Vs /2 width=1 by cpxs_fwd_cast/
#V #Vs #IHVs #W #T #U #H
elim (cpxs_inv_appl1 … H) -H *
[ -IHVs #V0 #T0 #_ #_ #H destruct /2 width=1/
| #b #W0 #T0 #HT0 #HU
  elim (IHVs … HT0) -IHVs -HT0 #HT0
  [ elim (tstc_inv_bind_appls_simple … HT0) //
  | @or3_intro1 -W (**) (* explicit constructor *)
    @(cpxs_trans … HU) -U
    @(cpxs_strap1 … (ⓐV.ⓛ{b}W0.T0)) /2 width=1/
  | @or3_intro2 -T (**) (* explicit constructor *)
    @(cpxs_trans … HU) -U
    @(cpxs_strap1 … (ⓐV.ⓛ{b}W0.T0)) /2 width=1/
  ]
| #b #V0 #V1 #V2 #T0 #HV0 #HV01 #HT0 #HU
  elim (IHVs … HT0) -IHVs -HT0 #HT0
  [ elim (tstc_inv_bind_appls_simple … HT0) //
  | @or3_intro1 -W (**) (* explicit constructor *)
    @(cpxs_trans … HU) -U
    @(cpxs_strap1 … (ⓐV0.ⓓ{b}V2.T0)) [ /2 width=1/ ] -V -Vs -T /2 width=3/
  | @or3_intro2 -T (**) (* explicit constructor *)
    @(cpxs_trans … HU) -U
    @(cpxs_strap1 … (ⓐV0.ⓓ{b}V2.T0)) [ /2 width=1/ ] -V -Vs -W /2 width=3/  
  ]
]
qed-.
