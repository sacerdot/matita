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

include "basic_2/rt_computation/cpxs_teqo_vector.ma".
include "basic_2/rt_computation/csx_simple_teqo.ma".
include "basic_2/rt_computation/csx_lsubr.ma".
include "basic_2/rt_computation/csx_lpx.ma".
include "basic_2/rt_computation/csx_vector.ma".

(* STRONGLY NORMALIZING TERM VECTORS FOR EXTENDED PARALLEL RT-TRANSITION ****)

(* Advanced properties ************************************* ****************)

(* Basic_1: was just: sn3_appls_beta *)
lemma csx_applv_beta (G) (L):
      ∀p,Vs,V,W,T. ❪G,L❫ ⊢ ⬈*𝐒 ⒶVs.ⓓ[p]ⓝW.V.T →
      ❪G,L❫ ⊢ ⬈*𝐒 ⒶVs.ⓐV.ⓛ[p]W.T.
#G #L #p #Vs elim Vs -Vs /2 width=1 by csx_appl_beta/
#V0 #Vs #IHV #V #W #T #H1T
lapply (csx_fwd_pair_sn … H1T) #HV0
lapply (csx_fwd_flat_dx … H1T) #H2T
@csx_appl_simple_teqo /2 width=1 by applv_simple, simple_flat/ -IHV -HV0 -H2T
#X #H #H0
elim (cpxs_fwd_beta_vector … H) -H #H
[ -H1T elim H0 -H0 //
| -H0 /3 width=5 by csx_cpxs_trans, cpxs_flat_dx/
]
qed.

lemma csx_applv_delta_drops (G) (L):
      ∀I,K,V1,i. ⇩[i] L ≘ K.ⓑ[I]V1 →
      ∀V2. ⇧[↑i] V1 ≘ V2 →
      ∀Vs. ❪G,L❫ ⊢ ⬈*𝐒 ⒶVs.V2 → ❪G,L❫ ⊢ ⬈*𝐒 ⒶVs.#i.
#G #L #I #K #V1 #i #HLK #V2 #HV12 #Vs elim Vs -Vs
[ /4 width=11 by csx_inv_lifts, csx_lref_pair_drops, drops_isuni_fwd_drop2/
| #V #Vs #IHV #H1T
  lapply (csx_fwd_pair_sn … H1T) #HV
  lapply (csx_fwd_flat_dx … H1T) #H2T
  @csx_appl_simple_teqo /2 width=1 by applv_simple, simple_atom/ -IHV -HV  -H2T
  #X #H #H0
  elim (cpxs_fwd_delta_drops_vector … HLK … HV12 … H) -HLK -HV12 -H #H
  [ -H1T elim H0 -H0 //
  | -H0 /3 width=5 by csx_cpxs_trans, cpxs_flat_dx/
  ]
]
qed.

(* Basic_1: was just: sn3_appls_abbr *)
lemma csx_applv_theta (G) (L):
      ∀p,V1b,V2b. ⇧[1] V1b ≘ V2b →
      ∀V,T. ❪G,L❫ ⊢ ⬈*𝐒 ⓓ[p]V.ⒶV2b.T → ❪G,L❫ ⊢ ⬈*𝐒 ⒶV1b.ⓓ[p]V.T.
#G #L #p #V1b #V2b * -V1b -V2b /2 width=1 by/
#V1b #V2b #V1 #V2 #HV12 #H
generalize in match HV12; -HV12 generalize in match V2; -V2 generalize in match V1; -V1
elim H -V1b -V2b /2 width=3 by csx_appl_theta/
#V1b #V2b #V1 #V2 #HV12 #HV12b #IHV12b #W1 #W2 #HW12 #V #T #H
lapply (csx_appl_theta … H … HW12) -H -HW12 #H
lapply (csx_fwd_pair_sn … H) #HW1
lapply (csx_fwd_flat_dx … H) #H1
@csx_appl_simple_teqo /2 width=3 by simple_flat/ -IHV12b -HW1 -H1 #X #H1 #H2
elim (cpxs_fwd_theta_vector … (V2⨮V2b) … H1) -H1 /2 width=1 by liftsv_cons/ -HV12b -HV12
[ -H #H elim H2 -H2 //
| -H2 /3 width=5 by csx_cpxs_trans, cpxs_flat_dx/
]
qed.

(* Basic_1: was just: sn3_appls_cast *)
lemma csx_applv_cast (G) (L):
      ∀Vs,U. ❪G,L❫ ⊢ ⬈*𝐒 ⒶVs.U →
      ∀T. ❪G,L❫ ⊢ ⬈*𝐒 ⒶVs.T → ❪G,L❫ ⊢ ⬈*𝐒 ⒶVs.ⓝU.T.
#G #L #Vs elim Vs -Vs /2 width=1 by csx_cast/
#V #Vs #IHV #U #H1U #T #H1T
lapply (csx_fwd_pair_sn … H1U) #HV
lapply (csx_fwd_flat_dx … H1U) #H2U
lapply (csx_fwd_flat_dx … H1T) #H2T
@csx_appl_simple_teqo /2 width=1 by applv_simple, simple_flat/ -IHV -HV -H2U -H2T
#X #H #H0
elim (cpxs_fwd_cast_vector … H) -H #H
[ -H1U -H1T elim H0 -H0 //
| -H1U -H0 /3 width=5 by csx_cpxs_trans, cpxs_flat_dx/
| -H1T -H0 /3 width=5 by csx_cpxs_trans, cpxs_flat_dx/
]
qed.
