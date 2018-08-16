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

include "static_2/syntax/theq_simple_vector.ma".
include "static_2/relocation/lifts_vector.ma".
include "basic_2/rt_computation/cpxs_theq.ma".

(* UNBOUND CONTEXT-SENSITIVE PARALLEL RT-COMPUTATION FOR TERMS **************)

(* Vector form of forward lemmas with head equivalence for terms ************)

lemma cpxs_fwd_sort_vector: ∀h,o,G,L,s,Vs,U. ⦃G, L⦄ ⊢ ⒶVs.⋆s ⬈*[h] U →
                            ⒶVs.⋆s ⩳[h, o] U ∨ ⦃G, L⦄ ⊢ ⒶVs.⋆(next h s) ⬈*[h] U.
#h #o #G #L #s #Vs elim Vs -Vs /2 width=1 by cpxs_fwd_sort/
#V #Vs #IHVs #U #H
elim (cpxs_inv_appl1 … H) -H *
[ -IHVs #V1 #T1 #_ #_ #H destruct /2 width=1 by theq_pair, or_introl/
| #p #W1 #T1 #HT1 #HU
  elim (IHVs … HT1) -IHVs -HT1 #HT1
  [ elim (theq_inv_applv_bind_simple … HT1) //
  | @or_intror (**) (* explicit constructor *)
    @(cpxs_trans … HU) -U
    @(cpxs_strap1 … (ⓐV.ⓛ{p}W1.T1)) /3 width=1 by cpxs_flat_dx, cpx_beta/
  ]
| #p #V1 #V2 #V3 #T1 #HV01 #HV12 #HT1 #HU
  elim (IHVs … HT1) -IHVs -HT1 #HT1
  [ elim (theq_inv_applv_bind_simple … HT1) //
  | @or_intror (**) (* explicit constructor *)
    @(cpxs_trans … HU) -U
    @(cpxs_strap1 … (ⓐV1.ⓓ{p}V3.T1)) /3 width=3 by cpxs_flat, cpx_theta/
  ]
]
qed-.

(* Basic_2A1: was: cpxs_fwd_delta_vector *)
lemma cpxs_fwd_delta_drops_vector: ∀h,o,I,G,L,K,V1,i. ⬇*[i] L ≘ K.ⓑ{I}V1 →
                                   ∀V2. ⬆*[↑i] V1 ≘ V2 →
                                   ∀Vs,U. ⦃G, L⦄ ⊢ ⒶVs.#i ⬈*[h] U →
                                   ⒶVs.#i ⩳[h, o] U ∨ ⦃G, L⦄ ⊢ ⒶVs.V2 ⬈*[h] U.
#h #o #I #G #L #K #V1 #i #HLK #V2 #HV12 #Vs elim Vs -Vs /2 width=5 by cpxs_fwd_delta_drops/
#V #Vs #IHVs #U #H -K -V1
elim (cpxs_inv_appl1 … H) -H *
[ -IHVs #V0 #T0 #_ #_ #H destruct /2 width=1 by theq_pair, or_introl/
| #q #W0 #T0 #HT0 #HU
  elim (IHVs … HT0) -IHVs -HT0 #HT0
  [ elim (theq_inv_applv_bind_simple … HT0) //
  | @or_intror -i (**) (* explicit constructor *)
    @(cpxs_trans … HU) -U
    @(cpxs_strap1 … (ⓐV.ⓛ{q}W0.T0)) /3 width=1 by cpxs_flat_dx, cpx_beta/
  ]
| #q #V0 #V1 #V3 #T0 #HV0 #HV01 #HT0 #HU
  elim (IHVs … HT0) -IHVs -HT0 #HT0
  [ elim (theq_inv_applv_bind_simple … HT0) //
  | @or_intror -i (**) (* explicit constructor *)
    @(cpxs_trans … HU) -U
    @(cpxs_strap1 … (ⓐV0.ⓓ{q}V3.T0)) /3 width=3 by cpxs_flat, cpx_theta/
  ]
]
qed-.

(* Basic_1: was just: pr3_iso_appls_beta *)
lemma cpxs_fwd_beta_vector: ∀h,o,p,G,L,Vs,V,W,T,U. ⦃G, L⦄ ⊢ ⒶVs.ⓐV.ⓛ{p}W.T ⬈*[h] U →
                            ⒶVs.ⓐV.ⓛ{p}W. T ⩳[h, o] U ∨ ⦃G, L⦄ ⊢ ⒶVs.ⓓ{p}ⓝW.V.T ⬈*[h] U.
#h #o #p #G #L #Vs elim Vs -Vs /2 width=1 by cpxs_fwd_beta/
#V0 #Vs #IHVs #V #W #T #U #H
elim (cpxs_inv_appl1 … H) -H *
[ -IHVs #V1 #T1 #_ #_ #H destruct /2 width=1 by theq_pair, or_introl/
| #q #W1 #T1 #HT1 #HU
  elim (IHVs … HT1) -IHVs -HT1 #HT1
  [ elim (theq_inv_applv_bind_simple … HT1) //
  | @or_intror (**) (* explicit constructor *)
    @(cpxs_trans … HU) -U
    @(cpxs_strap1 … (ⓐV0.ⓛ{q}W1.T1)) /3 width=1 by cpxs_flat_dx, cpx_beta/
  ]
| #q #V1 #V2 #V3 #T1 #HV01 #HV12 #HT1 #HU
  elim (IHVs … HT1) -IHVs -HT1 #HT1
  [ elim (theq_inv_applv_bind_simple … HT1) //
  | @or_intror (**) (* explicit constructor *)
    @(cpxs_trans … HU) -U
    @(cpxs_strap1 … (ⓐV1.ⓓ{q}V3.T1)) /3 width=3 by cpxs_flat, cpx_theta/
  ]
]
qed-.

(* Basic_1: was just: pr3_iso_appls_abbr *)
lemma cpxs_fwd_theta_vector: ∀h,o,G,L,V1b,V2b. ⬆*[1] V1b ≘ V2b →
                             ∀p,V,T,U. ⦃G, L⦄ ⊢ ⒶV1b.ⓓ{p}V.T ⬈*[h] U →
                             ⒶV1b.ⓓ{p}V.T ⩳[h, o] U ∨ ⦃G, L⦄ ⊢ ⓓ{p}V.ⒶV2b.T ⬈*[h] U.
#h #o #G #L #V1b #V2b * -V1b -V2b /3 width=1 by or_intror/
#V1b #V2b #V1a #V2a #HV12a #HV12b #p
generalize in match HV12a; -HV12a
generalize in match V2a; -V2a
generalize in match V1a; -V1a
elim HV12b -V1b -V2b /2 width=1 by cpxs_fwd_theta/
#V1b #V2b #V1b #V2b #HV12b #_ #IHV12b #V1a #V2a #HV12a #V #T #U #H
elim (cpxs_inv_appl1 … H) -H *
[ -IHV12b -HV12a -HV12b #V0 #T0 #_ #_ #H destruct /2 width=1 by theq_pair, or_introl/
| #q #W0 #T0 #HT0 #HU
  elim (IHV12b … HV12b … HT0) -IHV12b -HT0 #HT0
  [ -HV12a -HV12b -HU
    elim (theq_inv_pair1 … HT0) #V1 #T1 #H destruct
  | @or_intror -V1b (**) (* explicit constructor *)
    @(cpxs_trans … HU) -U
    elim (cpxs_inv_abbr1_dx … HT0) -HT0 *
    [ -HV12a #V1 #T1 #_ #_ #H destruct
    | -V1b #X #HT1 #H #H0 destruct
      elim (lifts_inv_bind1 … H) -H #W1 #T1 #HW01 #HT01 #H destruct
      @(cpxs_trans … (+ⓓV.ⓐV2a.ⓛ{q}W1.T1)) [ /3 width=1 by cpxs_flat_dx, cpxs_bind_dx/ ] -T -V2b -V2b
      @(cpxs_strap2 … (ⓐV1a.ⓛ{q}W0.T0))
      /4 width=7 by cpxs_beta_dx, cpx_zeta, lifts_bind, lifts_flat/
    ]
  ]
| #q #V0a #Va #V0 #T0 #HV10a #HV0a #HT0 #HU
  elim (IHV12b … HV12b … HT0) -HV12b -IHV12b -HT0 #HT0
  [ -HV12a -HV10a -HV0a -HU
    elim (theq_inv_pair1 … HT0) #V1 #T1 #H destruct
  | @or_intror -V1b -V1b (**) (* explicit constructor *)
    @(cpxs_trans … HU) -U
    elim (cpxs_inv_abbr1_dx … HT0) -HT0 *
    [ #V1 #T1 #HV1 #HT1 #H destruct
      lapply (cpxs_lifts_bi … HV10a (Ⓣ) … (L.ⓓV) … HV12a … HV0a) -V1a -V0a /3 width=1 by drops_refl, drops_drop/ #HV2a
      @(cpxs_trans … (ⓓ{p}V.ⓐV2a.T1)) /3 width=1 by cpxs_bind, cpxs_pair_sn, cpxs_flat_dx, cpxs_bind_dx/
    | #X #HT1 #H #H0 destruct
      elim (lifts_inv_bind1 … H) -H #V1 #T1 #HW01 #HT01 #H destruct
      lapply (cpxs_lifts_bi … HV10a (Ⓣ) … (L.ⓓV0) … HV12a … HV0a) -V0a /3 width=1 by drops_refl, drops_drop/ #HV2a
      @(cpxs_trans … (+ⓓV.ⓐV2a.ⓓ{q}V1.T1)) [ /3 width=1 by cpxs_flat_dx, cpxs_bind_dx/ ] -T -V2b -V2b
      @(cpxs_strap2 … (ⓐV1a.ⓓ{q}V0.T0)) [ /4 width=7 by cpx_zeta, lifts_bind, lifts_flat/ ] -V -V1 -T1
      @(cpxs_strap2 … (ⓓ{q}V0.ⓐV2a.T0)) /3 width=3 by cpxs_pair_sn, cpxs_bind_dx, cpx_theta/
    ]
  ]
]
qed-.

(* Basic_1: was just: pr3_iso_appls_cast *)
lemma cpxs_fwd_cast_vector: ∀h,o,G,L,Vs,W,T,U. ⦃G, L⦄ ⊢ ⒶVs.ⓝW.T ⬈*[h] U →
                            ∨∨ ⒶVs. ⓝW. T ⩳[h, o] U
                             | ⦃G, L⦄ ⊢ ⒶVs.T ⬈*[h] U
                             | ⦃G, L⦄ ⊢ ⒶVs.W ⬈*[h] U.
#h #o #G #L #Vs elim Vs -Vs /2 width=1 by cpxs_fwd_cast/
#V #Vs #IHVs #W #T #U #H
elim (cpxs_inv_appl1 … H) -H *
[ -IHVs #V0 #T0 #_ #_ #H destruct /2 width=1 by theq_pair, or3_intro0/
| #q #W0 #T0 #HT0 #HU elim (IHVs … HT0) -IHVs -HT0 #HT0
  [ elim (theq_inv_applv_bind_simple … HT0) //
  | @or3_intro1 -W (**) (* explicit constructor *)
    @(cpxs_trans … HU) -U
    @(cpxs_strap1 … (ⓐV.ⓛ{q}W0.T0)) /2 width=1 by cpxs_flat_dx, cpx_beta/
  | @or3_intro2 -T (**) (* explicit constructor *)
    @(cpxs_trans … HU) -U
    @(cpxs_strap1 … (ⓐV.ⓛ{q}W0.T0)) /2 width=1 by cpxs_flat_dx, cpx_beta/
  ]
| #q #V0 #V1 #V2 #T0 #HV0 #HV01 #HT0 #HU
  elim (IHVs … HT0) -IHVs -HT0 #HT0
  [ elim (theq_inv_applv_bind_simple … HT0) //
  | @or3_intro1 -W (**) (* explicit constructor *)
    @(cpxs_trans … HU) -U
    @(cpxs_strap1 … (ⓐV0.ⓓ{q}V2.T0)) /2 width=3 by cpxs_flat, cpx_theta/
  | @or3_intro2 -T (**) (* explicit constructor *)
    @(cpxs_trans … HU) -U
    @(cpxs_strap1 … (ⓐV0.ⓓ{q}V2.T0)) /2 width=3 by cpxs_flat, cpx_theta/
  ]
]
qed-.

(* Basic_1: was just: nf2_iso_appls_lref *)
lemma cpxs_fwd_cnx_vector: ∀h,o,G,L,T. 𝐒⦃T⦄ → ⦃G, L⦄ ⊢ ⬈[h, o] 𝐍⦃T⦄ →
                           ∀Vs,U. ⦃G, L⦄ ⊢ ⒶVs.T ⬈*[h] U → ⒶVs.T ⩳[h, o] U.
#h #o #G #L #T #H1T #H2T #Vs elim Vs -Vs [ @(cpxs_fwd_cnx … H2T) ] (**) (* /2 width=3 by cpxs_fwd_cnx/ does not work *)
#V #Vs #IHVs #U #H
elim (cpxs_inv_appl1 … H) -H *
[ -IHVs #V0 #T0 #_ #_ #H destruct /2 width=1 by theq_pair/
| #p #W0 #T0 #HT0 #HU
  lapply (IHVs … HT0) -IHVs -HT0 #HT0
  elim (theq_inv_applv_bind_simple … HT0) //
| #p #V1 #V2 #V0 #T0 #HV1 #HV12 #HT0 #HU
  lapply (IHVs … HT0) -IHVs -HT0 #HT0
  elim (theq_inv_applv_bind_simple … HT0) //
]
qed-.
