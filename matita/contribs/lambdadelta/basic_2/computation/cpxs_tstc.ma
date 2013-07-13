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

include "basic_2/grammar/tstc.ma".
include "basic_2/computation/lpxs_cpxs.ma".

(* CONTEXT-SENSITIVE EXTENDED PARALLEL COMPUTATION ON TERMS *****************)

(* Forward lemmas involving same top term constructor ***********************)

lemma cpxs_fwd_cnx: ∀h,g,L,T. ⦃h, L⦄ ⊢ 𝐍[g]⦃T⦄ → ∀U. ⦃h, L⦄ ⊢ T ➡*[g] U → T ≃ U.
#h #g #L #T #HT #U #H
>(cpxs_inv_cnx1 … H HT) -L -T //
qed-.

(* Basic_1: was just: pr3_iso_beta *)
lemma cpxs_fwd_beta: ∀h,g,a,L,V,W,T,U. ⦃h, L⦄ ⊢ ⓐV.ⓛ{a}W.T ➡*[g] U →
                     ⓐV.ⓛ{a}W.T ≃ U ∨ 
                     ∃∃T0. ⦃h, L.ⓛW⦄ ⊢ T ➡*[g] T0 & ⦃h, L⦄ ⊢ ⓓ{a}V.T0 ➡*[g] U.
#h #g #a #L #V #W #T #U #H
elim (cpxs_inv_appl1 … H) -H *
[ #V0 #T0 #_ #_ #H destruct /2 width=1/
| #b #V0 #W0 #T0 #HV0 #HT0 #HU
  elim (cpxs_inv_abst1 … HT0) -HT0 #W1 #T1 #_ #HT1 #H destruct -W1
  @or_intror @(ex2_intro … HT1) -W (**) (* explicit constructors *)
  @(cpxs_trans … HU) -U /2 width=1/
| #b #V1 #V2 #V0 #T1 #_ #_ #HT1 #_
  elim (cpxs_inv_abst1 … HT1) -HT1 #W2 #T2 #_ #_ #H destruct
]
qed-.

(* Note: probably this is an inversion lemma *)
lemma cpxs_fwd_delta: ∀h,g,I,L,K,V1,i. ⇩[0, i] L ≡ K.ⓑ{I}V1 →
                      ∀V2. ⇧[0, i + 1] V1 ≡ V2 →
                      ∀U. ⦃h, L⦄ ⊢ #i ➡*[g] U →
                      #i ≃ U ∨ ⦃h, L⦄ ⊢ V2 ➡*[g] U.
#h #g #I #L #K #V1 #i #HLK #V2 #HV12 #U #H
elim (cpxs_inv_lref1 … H) -H /2 width=1/
* #I0 #K0 #V0 #U0 #HLK0 #HVU0 #HU0
lapply (ldrop_mono … HLK0 … HLK) -HLK0 #H destruct
lapply (ldrop_fwd_ldrop2 … HLK) -HLK /3 width=9/
qed-.

lemma cpxs_fwd_theta: ∀h,g,a,L,V1,V,T,U. ⦃h, L⦄ ⊢ ⓐV1.ⓓ{a}V.T ➡*[g] U →
                      ∀V2. ⇧[0, 1] V1 ≡ V2 → ⓐV1.ⓓ{a}V.T ≃ U ∨
                      ⦃h, L⦄ ⊢ ⓓ{a}V.ⓐV2.T ➡*[g] U.
#h #g #a #L #V1 #V #T #U #H #V2 #HV12
elim (cpxs_inv_appl1 … H) -H *
[ -HV12 #V0 #T0 #_ #_ #H destruct /2 width=1/
| #b #V0 #W #T0 #HV10 #HT0 #HU
  elim (cpxs_inv_abbr1 … HT0) -HT0 *
  [ #V3 #T3 #_ #_ #H destruct
  | #X #HT2 #H #H0 destruct
    elim (lift_inv_bind1 … H) -H #W2 #T2 #HW2 #HT02 #H destruct
    @or_intror @(cpxs_trans … HU) -U (**) (* explicit constructor *)
    @(cpxs_trans … (+ⓓV.ⓐV2.ⓛ{b}W2.T2)) [ /3 width=1/ ] -T
    @(cpxs_strap2 … (ⓐV1.ⓛ{b}W.T0)) [ /5 width=7/ ] -V -V2 -W2 -T2
    @(cpxs_strap2 … (ⓓ{b}V1.T0)) [ /3 width=1/ ] -W /2 width=1/
  ]
| #b #V3 #V4 #V0 #T0 #HV13 #HV34 #HT0 #HU
  @or_intror @(cpxs_trans … HU) -U (**) (* explicit constructor *)
  elim (cpxs_inv_abbr1 … HT0) -HT0 *
  [ #V5 #T5 #HV5 #HT5 #H destruct
    lapply (cpxs_lift … HV13 (L.ⓓV) … HV12 … HV34) -V1 -V3 /2 width=1/
    /3 width=1/
  | #X #HT1 #H #H0 destruct
    elim (lift_inv_bind1 … H) -H #V5 #T5 #HV05 #HT05 #H destruct
    lapply (cpxs_lift … HV13 (L.ⓓV0) … HV12 … HV34) -V3 /2 width=1/ #HV24
    @(cpxs_trans … (+ⓓV.ⓐV2.ⓓ{b}V5.T5)) [ /3 width=1/ ] -T
    @(cpxs_strap2 … (ⓐV1.ⓓ{b}V0.T0)) [ /5 width=7/ ] -V -V5 -T5
    @(cpxs_strap2 … (ⓓ{b}V0.ⓐV2.T0)) [ /3 width=3/ ] -V1 /3 width=1/
  ]
]
qed-.

lemma cpxs_fwd_tau: ∀h,g,L,W,T,U. ⦃h, L⦄ ⊢ ⓝW.T ➡*[g] U →
                    ⓝW. T ≃ U ∨ ⦃h, L⦄ ⊢ T ➡*[g] U.
#h #g #L #W #T #U #H
elim (cpxs_inv_cast1 … H) -H /2 width=1/ *
#W0 #T0 #_ #_ #H destruct /2 width=1/
qed-.
