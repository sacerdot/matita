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
include "basic_2/computation/cprs_lift.ma".
include "basic_2/computation/cprs_lcprs.ma".

(* CONTEXT-SENSITIVE PARALLEL COMPUTATION ON TERMS **************************)

(* Forward lemmas involving same top term constructor ***********************)

(* Basic_1: was: pr3_iso_beta *)
lemma cprs_fwd_beta: ∀L,V,W,T,U. L ⊢ ⓐV. ⓛW. T ➡* U →
                     ⓐV. ⓛW. T ≃ U ∨ L ⊢ ⓓV. T ➡* U.
#L #V #W #T #U #H
elim (cprs_inv_appl1 … H) -H *
[ #V0 #T0 #_ #_ #H destruct /2 width=1/
| #V0 #W0 #T0 #HV0 #HT0 #HU
  elim (cprs_inv_abst1 Abbr V … HT0) -HT0 #W1 #T1 #_ #HT1 #H destruct -W1
  @or_intror -W
  @(cprs_trans … HU) -U /2 width=1/ (**) (* explicit constructor *)
| #V1 #V2 #V0 #T1 #_ #_ #HT1 #_
  elim (cprs_inv_abst1 Abbr V … HT1) -HT1 #W2 #T2 #_ #_ #H destruct
]
qed-.

(* Note: probably this is an inversion lemma *)
lemma cprs_fwd_delta: ∀L,K,V1,i. ⇩[0, i] L ≡ K. ⓓV1 →
                      ∀V2. ⇧[0, i + 1] V1 ≡ V2 →
                      ∀U. L ⊢ #i ➡* U →
                      #i ≃ U ∨ L ⊢ V2 ➡* U.
#L #K #V1 #i #HLK #V2 #HV12 #U #H
elim (cprs_inv_lref1 … H) -H /2 width=1/
* #K0 #V0 #U0 #HLK0 #HVU0 #HU0 #_
lapply (ldrop_mono … HLK0 … HLK) -HLK0 #H destruct
lapply (ldrop_fwd_ldrop2 … HLK) -HLK /3 width=9/
qed-.

lemma cprs_fwd_theta: ∀L,V1,V,T,U. L ⊢ ⓐV1. ⓓV. T ➡* U →
                      ∀V2. ⇧[0, 1] V1 ≡ V2 → ⓐV1. ⓓV. T ≃ U ∨
                      L ⊢ ⓓV. ⓐV2. T ➡* U.
#L #V1 #V #T #U #H #V2 #HV12
elim (cprs_inv_appl1 … H) -H *
[ -HV12 #V0 #T0 #_ #_ #H destruct /2 width=1/
| #V0 #W #T0 #HV10 #HT0 #HU
  elim (cprs_inv_abbr1 … HT0) -HT0 *
  [ #V3 #T3 #_ #_ #H destruct
  | #X #H #HT2
    elim (lift_inv_bind1 … H) -H #W2 #T2 #HW2 #HT02 #H destruct
    @or_intror @(cprs_trans … HU) -U (**) (* explicit constructor *)
    @(cprs_trans … (ⓓV.ⓐV2.ⓛW2.T2)) [ /3 width=1/ ] -T
    @(cprs_strap2 … (ⓐV1.ⓛW.T0)) [ /5 width=3/ ] -V -V2 -W2 -T2
    @(cprs_strap2 … (ⓓV1.T0)) [ /3 width=1/ ] -W /2 width=1/
  ]
| #V3 #V4 #V0 #T0 #HV13 #HV34 #HT0 #HU
  @or_intror @(cprs_trans … HU) -U (**) (* explicit constructor *)
  elim (cprs_inv_abbr1 … HT0) -HT0 *
  [ #V5 #T5 #HV5 #HT5 #H destruct
    lapply (cprs_lift (L.ⓓV) … HV12 … HV13 … HV34) -V1 -V3 /2 width=1/
    /3 width=1/
  | #X #H #HT1
    elim (lift_inv_bind1 … H) -H #V5 #T5 #HV05 #HT05 #H destruct
    lapply (cprs_lift (L.ⓓV0) … HV12 … HV13 … HV34) -V3 /2 width=1/ #HV24
    @(cprs_trans … (ⓓV.ⓐV2.ⓓV5.T5)) [ /3 width=1/ ] -T
    @(cprs_strap2 … (ⓐV1.ⓓV0.T0)) [ /5 width=3/ ] -V -V5 -T5
    @(cprs_strap2 … (ⓓV0.ⓐV2.T0)) [ /3 width=3/ ] -V1 /3 width=9/
  ]
]
qed-.

lemma cprs_fwd_tau: ∀L,W,T,U. L ⊢ ⓣW. T ➡* U →
                    ⓣW. T ≃ U ∨ L ⊢ T ➡* U.
#L #W #T #U #H
elim (cprs_inv_cast1 … H) -H /2 width=1/ *
#W0 #T0 #_ #_ #H destruct /2 width=1/
qed-.
