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

(* Basic_1: was only: sn3_appls_lref *)
lemma csn_applv_cnf: ∀L,T. 𝐒⦃T⦄ → L ⊢ 𝐍⦃T⦄ → 
                     ∀Vs. L ⊢ ⬇* Vs → L ⊢ ⬇* ⒶVs.T.
#L #T #H1T #H2T #Vs elim Vs -Vs [ #_ @(csn_cnf … H2T) ] (**) (* /2 width=1/ does not work *)
#V #Vs #IHV #H
elim (csnv_inv_cons … H) -H #HV #HVs
@csn_appl_simple_tstc // -HV /2 width=1/ -IHV -HVs
#X #H #H0
lapply (cprs_fwd_cnf_vector … H) -H // -H1T -H2T #H
elim (H0 ?) -H0 //
qed.

(* Basic_1: was: sn3_appls_beta *)
lemma csn_applv_beta: ∀L,W. L ⊢ ⬇* W →
                      ∀Vs,V,T. L ⊢ ⬇* ⒶVs.ⓓV.T →
                      L ⊢ ⬇* ⒶVs. ⓐV.ⓛW. T.
#L #W #HW #Vs elim Vs -Vs /2 width=1/ -HW
#V0 #Vs #IHV #V #T #H1T
lapply (csn_fwd_pair_sn … H1T) #HV0
lapply (csn_fwd_flat_dx … H1T) #H2T
@csn_appl_simple_tstc // -HV0 /2 width=1/ -IHV -H2T
#X #H #H0
elim (cprs_fwd_beta_vector … H) -H #H
[ -H1T elim (H0 ?) -H0 //
| -H0 @(csn_cprs_trans … H1T) -H1T /2 width=1/
]
qed.

lemma csn_applv_delta: ∀L,K,V1,i. ⇩[0, i] L ≡ K. ⓓV1 →
                       ∀V2. ⇧[0, i + 1] V1 ≡ V2 →
                       ∀Vs.L ⊢ ⬇* (ⒶVs. V2) → L ⊢ ⬇* (ⒶVs. #i).
#L #K #V1 #i #HLK #V2 #HV12 #Vs elim Vs -Vs
[ #H
  lapply (ldrop_fwd_ldrop2 … HLK) #HLK0
  lapply (csn_inv_lift … H … HLK0 HV12) -V2 -HLK0 /2 width=4/
| #V #Vs #IHV #H1T
  lapply (csn_fwd_pair_sn … H1T) #HV
  lapply (csn_fwd_flat_dx … H1T) #H2T
  @csn_appl_simple_tstc // -HV /2 width=1/ -IHV -H2T
  #X #H #H0
  elim (cprs_fwd_delta_vector … HLK … HV12 … H) -HLK -HV12 -H #H
  [ -H1T elim (H0 ?) -H0 //
  | -H0 @(csn_cprs_trans … H1T) -H1T /2 width=1/
  ]
]
qed.

(* Basic_1: was: sn3_appls_abbr *) 
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
elim (cprs_fwd_theta_vector … (V2@V2s) … H1) -H1 /2 width=1/ -HV12s -HV12
[ -H #H elim (H2 ?) -H2 //
| -H2 #H1 @(csn_cprs_trans … H) -H /2 width=1/
]
qed.

(* Basic_1: was: sn3_appls_cast *)
lemma csn_applv_tau: ∀L,W. L ⊢ ⬇* W →
                     ∀Vs,T. L ⊢ ⬇* ⒶVs. T →
                     L ⊢ ⬇* ⒶVs. ⓣW. T.
#L #W #HW #Vs elim Vs -Vs /2 width=1/ -HW
#V #Vs #IHV #T #H1T
lapply (csn_fwd_pair_sn … H1T) #HV
lapply (csn_fwd_flat_dx … H1T) #H2T
@csn_appl_simple_tstc // -HV /2 width=1/ -IHV -H2T
#X #H #H0
elim (cprs_fwd_tau_vector … H) -H #H
[ -H1T elim (H0 ?) -H0 //
| -H0 @(csn_cprs_trans … H1T) -H1T /2 width=1/
]
qed.

theorem csn_acr: acr cpr (eq …) (csn …) (λL,T. L ⊢ ⬇* T).
@mk_acr //
[ /3 width=1/
| /2 width=1/
| /2 width=6/
| #L #V1 #V2 #HV12 #V #T #H #HVT
  @(csn_applv_theta … HV12) -HV12 //
  @(csn_abbr) //
| /2 width=1/
| @csn_lift
]
qed.
