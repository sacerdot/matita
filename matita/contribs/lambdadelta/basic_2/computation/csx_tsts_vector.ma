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

include "basic_2/computation/gcp_cr.ma".
include "basic_2/computation/cpxs_tsts_vector.ma".
include "basic_2/computation/csx_lpx.ma".
include "basic_2/computation/csx_vector.ma".

(* CONTEXT-SENSITIVE EXTENDED STRONGLY NORMALIZING TERM VECTORS *************)

(* Advanced properties ******************************************************)

(* Basic_1: was just: sn3_appls_lref *)
lemma csx_applv_cnx: ∀h,g,G,L,T. 𝐒⦃T⦄ → ⦃G, L⦄ ⊢ ➡[h, g] 𝐍⦃T⦄ →
                     ∀Vs. ⦃G, L⦄ ⊢ ⬊*[h, g] Vs → ⦃G, L⦄ ⊢ ⬊*[h, g] ⒶVs.T.
#h #g #G #L #T #H1T #H2T #Vs elim Vs -Vs [ #_ @(cnx_csx … H2T) ] (**) (* /2 width=1/ does not work *)
#V #Vs #IHV #H
elim (csxv_inv_cons … H) -H #HV #HVs
@csx_appl_simple_tsts /2 width=1 by applv_simple/ -IHV -HV -HVs
#X #H #H0
lapply (cpxs_fwd_cnx_vector … H) -H // -H1T -H2T #H
elim (H0) -H0 //
qed.

lemma csx_applv_sort: ∀h,g,G,L,k,Vs. ⦃G, L⦄ ⊢ ⬊*[h, g] Vs → ⦃G, L⦄ ⊢ ⬊*[h, g] ⒶVs.⋆k.
#h #g #G #L #k elim (deg_total h g k)
#l generalize in match k; -k @(nat_ind_plus … l) -l [ /3 width=6 by csx_applv_cnx, cnx_sort, simple_atom/ ]
#l #IHl #k #Hkl lapply (deg_next_SO … Hkl) -Hkl
#Hkl #Vs elim Vs -Vs /2 width=1 by/
#V #Vs #IHVs #HVVs
elim (csxv_inv_cons … HVVs) #HV #HVs
@csx_appl_simple_tsts /2 width=1 by applv_simple, simple_atom/ -IHVs -HV -HVs
#X #H #H0
elim (cpxs_fwd_sort_vector … H) -H #H
[ elim H0 -H0 //
| -H0 @(csx_cpxs_trans … (Ⓐ(V@Vs).⋆(next h k))) /2 width=1 by cpxs_flat_dx/
]
qed.

(* Basic_1: was just: sn3_appls_beta *)
lemma csx_applv_beta: ∀h,g,a,G,L,Vs,V,W,T. ⦃G, L⦄ ⊢ ⬊*[h, g] ⒶVs.ⓓ{a}ⓝW.V.T →
                      ⦃G, L⦄ ⊢ ⬊*[h, g] ⒶVs. ⓐV.ⓛ{a}W.T.
#h #g #a #G #L #Vs elim Vs -Vs /2 width=1 by csx_appl_beta/
#V0 #Vs #IHV #V #W #T #H1T
lapply (csx_fwd_pair_sn … H1T) #HV0
lapply (csx_fwd_flat_dx … H1T) #H2T
@csx_appl_simple_tsts /2 width=1 by applv_simple, simple_flat/ -IHV -HV0 -H2T
#X #H #H0
elim (cpxs_fwd_beta_vector … H) -H #H
[ -H1T elim H0 -H0 //
| -H0 /3 width=5 by csx_cpxs_trans, cpxs_flat_dx/
]
qed.

lemma csx_applv_delta: ∀h,g,I,G,L,K,V1,i. ⇩[i] L ≡ K.ⓑ{I}V1 →
                       ∀V2. ⇧[0, i + 1] V1 ≡ V2 →
                       ∀Vs. ⦃G, L⦄ ⊢ ⬊*[h, g] (ⒶVs.V2) → ⦃G, L⦄ ⊢ ⬊*[h, g] (ⒶVs.#i).
#h #g #I #G #L #K #V1 #i #HLK #V2 #HV12 #Vs elim Vs -Vs
[ /4 width=12 by csx_inv_lift, csx_lref_bind, drop_fwd_drop2/
| #V #Vs #IHV #H1T
  lapply (csx_fwd_pair_sn … H1T) #HV
  lapply (csx_fwd_flat_dx … H1T) #H2T
  @csx_appl_simple_tsts /2 width=1 by applv_simple, simple_atom/ -IHV -HV  -H2T
  #X #H #H0
  elim (cpxs_fwd_delta_vector … HLK … HV12 … H) -HLK -HV12 -H #H
  [ -H1T elim H0 -H0 //
  | -H0 /3 width=5 by csx_cpxs_trans, cpxs_flat_dx/
  ]
]
qed.

(* Basic_1: was just: sn3_appls_abbr *)
lemma csx_applv_theta: ∀h,g,a,G,L,V1s,V2s. ⇧[0, 1] V1s ≡ V2s →
                       ∀V,T. ⦃G, L⦄ ⊢ ⬊*[h, g] ⓓ{a}V.ⒶV2s.T →
                       ⦃G, L⦄ ⊢ ⬊*[h, g] ⒶV1s.ⓓ{a}V.T.
#h #g #a #G #L #V1s #V2s * -V1s -V2s /2 width=1 by/
#V1s #V2s #V1 #V2 #HV12 #H
generalize in match HV12; -HV12 generalize in match V2; -V2 generalize in match V1; -V1
elim H -V1s -V2s /2 width=3 by csx_appl_theta/
#V1s #V2s #V1 #V2 #HV12 #HV12s #IHV12s #W1 #W2 #HW12 #V #T #H
lapply (csx_appl_theta … HW12 … H) -H -HW12 #H
lapply (csx_fwd_pair_sn … H) #HW1
lapply (csx_fwd_flat_dx … H) #H1
@csx_appl_simple_tsts /2 width=3 by simple_flat/ -IHV12s -HW1 -H1 #X #H1 #H2
elim (cpxs_fwd_theta_vector … (V2@V2s) … H1) -H1 /2 width=1 by liftv_cons/ -HV12s -HV12
[ -H #H elim H2 -H2 //
| -H2 /3 width=5 by csx_cpxs_trans, cpxs_flat_dx/
]
qed.

(* Basic_1: was just: sn3_appls_cast *)
lemma csx_applv_cast: ∀h,g,G,L,Vs,W,T. ⦃G, L⦄ ⊢ ⬊*[h, g] ⒶVs.W → ⦃G, L⦄ ⊢ ⬊*[h, g] ⒶVs.T →
                      ⦃G, L⦄ ⊢ ⬊*[h, g] ⒶVs.ⓝW.T.
#h #g #G #L #Vs elim Vs -Vs /2 width=1 by csx_cast/
#V #Vs #IHV #W #T #H1W #H1T
lapply (csx_fwd_pair_sn … H1W) #HV
lapply (csx_fwd_flat_dx … H1W) #H2W
lapply (csx_fwd_flat_dx … H1T) #H2T
@csx_appl_simple_tsts /2 width=1 by applv_simple, simple_flat/ -IHV -HV -H2W -H2T
#X #H #H0
elim (cpxs_fwd_cast_vector … H) -H #H
[ -H1W -H1T elim H0 -H0 //
| -H1W -H0 /3 width=5 by csx_cpxs_trans, cpxs_flat_dx/
| -H1T -H0 /3 width=5 by csx_cpxs_trans, cpxs_flat_dx/
]
qed.

theorem csx_gcr: ∀h,g. gcr (cpx h g) (eq …) (csx h g) (csx h g).
#h #g @mk_gcr //
[ /2 width=8 by csx_lift/
| /3 width=1 by csx_applv_cnx/
|3,4,7: /2 width=1 by csx_applv_beta, csx_applv_sort, csx_applv_cast/
| /2 width=7 by csx_applv_delta/
| #G #L #V1s #V2s #HV12s #a #V #T #H #HV
  @(csx_applv_theta … HV12s) -HV12s
  @csx_abbr //
]
qed.
