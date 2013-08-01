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
include "basic_2/computation/cpxs_tstc_vector.ma".
include "basic_2/computation/csn_lpx.ma".
include "basic_2/computation/csn_vector.ma".

(* CONTEXT-SENSITIVE EXTENDED STRONGLY NORMALIZING TERM VECTORS *************)

(* Advanced properties ******************************************************)

(* Basic_1: was just: sn3_appls_lref *)
lemma csn_applv_cnx: ∀h,g,L,T. 𝐒⦃T⦄ → ⦃G, L⦄ ⊢ 𝐍[h, g]⦃T⦄ →
                     ∀Vs. ⦃G, L⦄ ⊢ ⬊*[h, g] Vs → ⦃G, L⦄ ⊢ ⬊*[h, g] ⒶVs.T.
#h #g #L #T #H1T #H2T #Vs elim Vs -Vs [ #_ @(cnx_csn … H2T) ] (**) (* /2 width=1/ does not work *)
#V #Vs #IHV #H
elim (csnv_inv_cons … H) -H #HV #HVs
@csn_appl_simple_tstc // -HV /2 width=1/ -IHV -HVs
#X #H #H0
lapply (cpxs_fwd_cnx_vector … H) -H // -H1T -H2T #H
elim (H0) -H0 //
qed.

lemma csn_applv_sort: ∀h,g,L,k,Vs. ⦃G, L⦄ ⊢ ⬊*[h, g] Vs → ⦃G, L⦄ ⊢ ⬊*[h, g] ⒶVs.⋆k.
#h #g #L #k elim (deg_total h g k)
#l generalize in match k; -k @(nat_ind_plus … l) -l [ /3 width=1/ ]
#l #IHl #k #Hkl lapply (deg_next_SO … Hkl) -Hkl
#Hkl #Vs elim Vs -Vs /2 width=1/
#V #Vs #IHVs #HVVs
elim (csnv_inv_cons … HVVs) #HV #HVs
@csn_appl_simple_tstc // -HV /2 width=1/ -IHVs -HVs
#X #H #H0
elim (cpxs_fwd_sort_vector … H) -H #H
[ elim H0 -H0 //
| -H0 @(csn_cpxs_trans … (Ⓐ(V@Vs).⋆(next h k))) /2 width=1/
]
qed.

(* Basic_1: was just: sn3_appls_beta *)
lemma csn_applv_beta: ∀h,g,a,L,Vs,V,W,T. ⦃G, L⦄ ⊢ ⬊*[h, g] ⒶVs.ⓓ{a}ⓝW.V.T →
                      ⦃G, L⦄ ⊢ ⬊*[h, g] ⒶVs. ⓐV.ⓛ{a}W.T.
#h #g #a #L #Vs elim Vs -Vs /2 width=1/
#V0 #Vs #IHV #V #W #T #H1T
lapply (csn_fwd_pair_sn … H1T) #HV0
lapply (csn_fwd_flat_dx … H1T) #H2T
@csn_appl_simple_tstc // -HV0 /2 width=1/ -IHV -H2T
#X #H #H0
elim (cpxs_fwd_beta_vector … H) -H #H
[ -H1T elim H0 -H0 //
| -H0 @(csn_cpxs_trans … H1T) -H1T /2 width=1/
]
qed.

lemma csn_applv_delta: ∀h,g,I,L,K,V1,i. ⇩[0, i] L ≡ K.ⓑ{I}V1 →
                       ∀V2. ⇧[0, i + 1] V1 ≡ V2 →
                       ∀Vs. ⦃G, L⦄ ⊢ ⬊*[h, g] (ⒶVs.V2) → ⦃G, L⦄ ⊢ ⬊*[h, g] (ⒶVs.#i).
#h #g #I #L #K #V1 #i #HLK #V2 #HV12 #Vs elim Vs -Vs
[ #H
  lapply (ldrop_fwd_ldrop2 … HLK) #HLK0
  lapply (csn_inv_lift … H … HLK0 HV12) -V2 -HLK0 /2 width=5/
| #V #Vs #IHV #H1T
  lapply (csn_fwd_pair_sn … H1T) #HV
  lapply (csn_fwd_flat_dx … H1T) #H2T
  @csn_appl_simple_tstc // -HV /2 width=1/ -IHV -H2T
  #X #H #H0
  elim (cpxs_fwd_delta_vector … HLK … HV12 … H) -HLK -HV12 -H #H
  [ -H1T elim H0 -H0 //
  | -H0 @(csn_cpxs_trans … H1T) -H1T /2 width=1/
  ]
]
qed.

(* Basic_1: was just: sn3_appls_abbr *)
lemma csn_applv_theta: ∀h,g,a,L,V1s,V2s. ⇧[0, 1] V1s ≡ V2s →
                       ∀V,T. ⦃G, L⦄ ⊢ ⬊*[h, g] ⓓ{a}V.ⒶV2s.T →
                       ⦃G, L⦄ ⊢ ⬊*[h, g] ⒶV1s.ⓓ{a}V.T.
#h #g #a #L #V1s #V2s * -V1s -V2s /2 width=1/
#V1s #V2s #V1 #V2 #HV12 #H
generalize in match HV12; -HV12 generalize in match V2; -V2 generalize in match V1; -V1
elim H -V1s -V2s /2 width=3/
#V1s #V2s #V1 #V2 #HV12 #HV12s #IHV12s #W1 #W2 #HW12 #V #T #H
lapply (csn_appl_theta … HW12 … H) -H -HW12 #H
lapply (csn_fwd_pair_sn … H) #HW1
lapply (csn_fwd_flat_dx … H) #H1
@csn_appl_simple_tstc // -HW1 /2 width=3/ -IHV12s -H1 #X #H1 #H2
elim (cpxs_fwd_theta_vector … (V2@V2s) … H1) -H1 /2 width=1/ -HV12s -HV12
[ -H #H elim H2 -H2 //
| -H2 #H1 @(csn_cpxs_trans … H) -H /2 width=1/
]
qed.

(* Basic_1: was just: sn3_appls_cast *)
lemma csn_applv_cast: ∀h,g,L,Vs,W,T. ⦃G, L⦄ ⊢ ⬊*[h, g] ⒶVs.W → ⦃G, L⦄ ⊢ ⬊*[h, g] ⒶVs.T →
                      ⦃G, L⦄ ⊢ ⬊*[h, g] ⒶVs.ⓝW.T.
#h #g #L #Vs elim Vs -Vs /2 width=1/
#V #Vs #IHV #W #T #H1W #H1T
lapply (csn_fwd_pair_sn … H1W) #HV
lapply (csn_fwd_flat_dx … H1W) #H2W
lapply (csn_fwd_flat_dx … H1T) #H2T
@csn_appl_simple_tstc // -HV /2 width=1/ -IHV -H2W -H2T
#X #H #H0
elim (cpxs_fwd_cast_vector … H) -H #H
[ -H1W -H1T elim H0 -H0 //
| -H1W -H0 @(csn_cpxs_trans … H1T) -H1T /2 width=1/
| -H1T -H0 @(csn_cpxs_trans … H1W) -H1W /2 width=1/
]
qed.

theorem csn_acr: ∀h,g. acr (cpx h g) (eq …) (csn h g) (λL,T. ⦃G, L⦄ ⊢ ⬊*[h, g] T).
#h #g @mk_acr //
[ /3 width=1/
|2,3,6: /2 width=1/
| /2 width=7/
| #L #V1s #V2s #HV12s #a #V #T #H #HV
  @(csn_applv_theta … HV12s) -HV12s
  @(csn_abbr) //
| @csn_lift
]
qed.
