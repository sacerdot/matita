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

include "basic_2/computation/acp_cr.ma".
include "basic_2/computation/cprs_tstc_vector.ma".
include "basic_2/computation/csn_lcpr.ma".
include "basic_2/computation/csn_vector.ma".

(* CONTEXT-SENSITIVE STRONGLY NORMALIZING TERM VECTORS **********************)

(* Advanced properties ******************************************************)
(*
(* Basic_1: was only: sn3_appl_appls *)
lemma csn_appl_appls_simple_tstc: ∀L,Vs,V,T1. L ⊢ ⬇* V → L ⊢ ⬇* T1 →
                                  (∀T2. L ⊢ ⒶVs.T1 ➡* T2 → (ⒶVs.T1 ≃ T2 → False) → L ⊢ ⬇* ⓐV. T2) →
                                  𝐒[T1] → L ⊢ ⬇* ⓐV. ⒶVs. T1.
#L *
[ #V #T1 #HV
  @csn_appl_simple_tstc //
| #V0 #Vs #V #T1 #HV #H1T1 #H2T1 #H3T1
  @csn_appl_simple_tstc // -HV
  [ @H2T1
]
qed.
*)
lemma csn_applv_theta: ∀L,V1s,V2s. ⇧[0, 1] V1s ≡ V2s →
                       ∀V,T. L ⊢ ⬇* ⓓV. ⒶV2s. T → L ⊢ ⬇* V →
                       L ⊢ ⬇* ⒶV1s. ⓓV. T.
#L #V1s #V2s * -V1s -V2s /2 width=1/
#V1s #V2s #V1 #V2 #HV12 #H 
generalize in match HV12; -HV12 generalize in match V2; -V2 generalize in match V1; -V1
elim H -V1s -V2s /2 width=3/
#V1s #V2s #V1 #V2 #HV12 #HV12s #IHV12s #W1 #W2 #HW12 #V #T #H #HV
lapply (csn_appl_theta … HW12 … H) -H -HW12 #H
lapply (csn_fwd_pair_sn … H) #HW1
lapply (csn_fwd_flat_dx … H) #H1
@csn_appl_simple_tstc // -HW1 /2 width=3/ -IHV12s -HV -H1 #X #H1 #H2
elim (cprs_fwd_theta_vector … (V2::V2s) … H1) -H1 /2 width=1/ -HV12s -HV12
[ -H #H elim (H2 ?) -H2 //
| -H2 #H1 @(csn_cprs_trans … H) -H /2 width=1/
]
qed.

lemma csn_applv_tau: ∀L,W. L ⊢ ⬇* W →
                     ∀Vs,T. L ⊢ ⬇* ⒶVs. T →
                     L ⊢ ⬇* ⒶVs. ⓣW. T.
#L #W #HW #Vs elim Vs -Vs /2 width=1/ -HW
#V #Vs #IHV #T #H1T
lapply (csn_fwd_pair_sn … H1T) #HV
lapply (csn_fwd_flat_dx … H1T) #H2T
@csn_appl_simple_tstc // -HV /2 width=1/ -IHV -H2T
[ #X #H #H0
  elim (cprs_fwd_tau_vector … H) -H #H
  [ -H1T elim (H0 ?) -H0 //
  | -H0 @(csn_cprs_trans … H1T) -H1T /2 width=1/
  ]
| -H1T elim Vs -Vs //
]
qed.
(*
theorem csn_acr: acr cpr (eq …) (csn …) (λL,T. L ⊢ ⬇* T).
@mk_acr //
[
|
|
| #L #V1 #V2 #HV12 #V #T #H #HVT
  @(csn_applv_theta … HV12) -HV12 //
  @(csn_abbr) //
| /2 width=1/
| @csn_lift
]
qed.
*)
axiom csn_acr: acr cpr (eq …) (csn …) (λL,T. L ⊢ ⬇* T).
