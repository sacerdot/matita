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

include "Basic_2/grammar/tstc_vector.ma".
include "Basic_2/substitution/lift_vector.ma".
include "Basic_2/computation/cprs_tstc.ma".

(* CONTEXT-SENSITIVE PARALLEL COMPUTATION ON TERMS **************************)

(* Vector form of forward lemmas involving same top term constructor ********)
(*
lemma cpr_fwd_beta_vector: ∀L,V,W,T,U,Vs. L ⊢ ⒶVs. ⓐV. ⓛW. T ➡ U →
                           ⒶVs. ⓐV. ⓛW. T ≃ U ∨ L ⊢ ⒶVs. ⓓV. T ➡* U.
#L #V #W #T #U * /2 width=1 by cpr_fwd_beta/
#V0 #Vs #H
elim (cpr_inv_appl1_simple … H ?) -H
[ #V1 #T1 #_ #_ #H destruct /2 width=1/
| elim Vs -Vs //
]
qed-.

lemma cpr_fwd_theta_vector: ∀L,V1s,V2s. ⇧[0, 1] V1s ≡ V2s →
                            ∀V,T,U. L ⊢ ⒶV1s. ⓓV. T ➡ U →
                            ⒶV1s. ⓓV. T ≃ U ∨ L ⊢ ⓓV. ⒶV2s. T ➡* U.
#L #V1s #V2s * -V1s -V2s /3 width=1/
#V1s #V2s #V1a #V2a #HV12a * -V1s -V2s /2 width=1 by cpr_fwd_theta/ -HV12a
#V1s #V2s #V1b #V2b #_ #_ #V #U #T #H
elim (cpr_inv_appl1_simple … H ?) -H //
#V0 #T0 #_ #_ #H destruct /2 width=1/
qed-.
*)

(* Basic_1: was: pr3_iso_appls_cast *)
lemma cprs_fwd_tau_vector: ∀L,Vs,W,T,U. L ⊢ ⒶVs. ⓣW. T ➡* U →
                           ⒶVs. ⓣW. T ≃ U ∨ L ⊢ ⒶVs. T ➡* U.
#L #Vs elim Vs -Vs /2 width=1 by cprs_fwd_tau/
#V #Vs #IHVs #W #T #U #H
elim (cprs_inv_appl1 … H) -H *
[ -IHVs #V0 #T0 #_ #_ #H destruct /2 width=1/
| #V0 #W0 #T0 #HV0 #HT0 #HU
  elim (IHVs … HT0) -IHVs -HT0 #HT0
  [ elim (tstc_inv_bind_appls_simple … HT0 ?) //
  | @or_intror
    @(cprs_trans … HU) -HU
    @(cprs_strap1 … (ⓐV0.ⓛW0.T0)) /2 width=1/ -HV0 -HT0 /3 width=1/
  ]
| #V0 #V1 #V2 #T0 #HV0 #HV01 #HT0 #HU
  elim (IHVs … HT0) -IHVs -HT0 #HT0
  [ elim (tstc_inv_bind_appls_simple … HT0 ?) //
  | @or_intror
    @(cprs_trans … HU) -HU
    @(cprs_strap1 … (ⓐV0.ⓓV2.T0)) /2 width=1/ -HV0 -HT0 /3 width=3/
]
qed-.

axiom cprs_fwd_theta_vector: ∀L,V1s,V2s. ⇧[0, 1] V1s ≡ V2s →
                            ∀V,T,U. L ⊢ ⒶV1s. ⓓV. T ➡* U →
                            ⒶV1s. ⓓV. T ≃ U ∨ L ⊢ ⓓV. ⒶV2s. T ➡* U.
