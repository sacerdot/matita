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
(*
include "basic_2/computation/gcp_cr.ma".
*)
include "basic_2/rt_computation/cpxs_theq_vector.ma".
include "basic_2/rt_computation/csx_vector.ma".
include "basic_2/rt_computation/csx_theq.ma".
include "basic_2/rt_computation/csx_lfpx.ma".

(* STRONGLY NORMALIZING TERMS FOR UNCOUNTED PARALLEL RT-TRANSITION **********)

(* Vector form of properties with head equivalence for terms ****************)
(*
*)
(*
*)

(* Basic_1: was just: sn3_appls_beta *)
lemma csx_applv_beta: ∀h,o,p,G,L,Vs,V,W,T. ⦃G, L⦄ ⊢ ⬈*[h, o] ⒶVs.ⓓ{p}ⓝW.V.T →
                      ⦃G, L⦄ ⊢ ⬈*[h, o] ⒶVs. ⓐV.ⓛ{p}W.T.
#h #o #a #G #L #Vs elim Vs -Vs /2 width=1 by csx_appl_beta/
#V0 #Vs #IHV #V #W #T #H1T
lapply (csx_fwd_pair_sn … H1T) #HV0
lapply (csx_fwd_flat_dx … H1T) #H2T
@csx_appl_simple_theq /2 width=1 by applv_simple, simple_flat/ -IHV -HV0 -H2T
#X #H #H0
elim (cpxs_fwd_beta_vector … H) -H #H
[ -H1T elim H0 -H0 //
| -H0 /3 width=5 by csx_cpxs_trans, cpxs_flat_dx/
]
qed.

lemma csx_applv_delta: ∀h,o,I,G,L,K,V1,i. ⬇[i] L ≡ K.ⓑ{I}V1 →
                       ∀V2. ⬆[0, i + 1] V1 ≡ V2 →
                       ∀Vs. ⦃G, L⦄ ⊢ ⬈*[h, o] (ⒶVs.V2) → ⦃G, L⦄ ⊢ ⬈*[h, o] (ⒶVs.#i).
#h #o #I #G #L #K #V1 #i #HLK #V2 #HV12 #Vs elim Vs -Vs
[ /4 width=12 by csx_inv_lift, csx_lref_bind, drop_fwd_drop2/
| #V #Vs #IHV #H1T
  lapply (csx_fwd_pair_sn … H1T) #HV
  lapply (csx_fwd_flat_dx … H1T) #H2T
  @csx_appl_simple_theq /2 width=1 by applv_simple, simple_atom/ -IHV -HV  -H2T
  #X #H #H0
  elim (cpxs_fwd_delta_vector … HLK … HV12 … H) -HLK -HV12 -H #H
  [ -H1T elim H0 -H0 //
  | -H0 /3 width=5 by csx_cpxs_trans, cpxs_flat_dx/
  ]
]
qed.

(* Basic_1: was just: sn3_appls_abbr *)
lemma csx_applv_theta: ∀h,o,a,G,L,V1b,V2b. ⬆[0, 1] V1b ≡ V2b →
                       ∀V,T. ⦃G, L⦄ ⊢ ⬈*[h, o] ⓓ{a}V.ⒶV2b.T →
                       ⦃G, L⦄ ⊢ ⬈*[h, o] ⒶV1b.ⓓ{a}V.T.
#h #o #a #G #L #V1b #V2b * -V1b -V2b /2 width=1 by/
#V1b #V2b #V1 #V2 #HV12 #H
generalize in match HV12; -HV12 generalize in match V2; -V2 generalize in match V1; -V1
elim H -V1b -V2b /2 width=3 by csx_appl_theta/
#V1b #V2b #V1 #V2 #HV12 #HV12b #IHV12b #W1 #W2 #HW12 #V #T #H
lapply (csx_appl_theta … HW12 … H) -H -HW12 #H
lapply (csx_fwd_pair_sn … H) #HW1
lapply (csx_fwd_flat_dx … H) #H1
@csx_appl_simple_theq /2 width=3 by simple_flat/ -IHV12b -HW1 -H1 #X #H1 #H2
elim (cpxs_fwd_theta_vector … (V2@V2b) … H1) -H1 /2 width=1 by liftv_cons/ -HV12b -HV12
[ -H #H elim H2 -H2 //
| -H2 /3 width=5 by csx_cpxs_trans, cpxs_flat_dx/
]
qed.

(* Basic_1: was just: sn3_appls_cast *)
lemma csx_applv_cast: ∀h,o,G,L,Vs,W,T. ⦃G, L⦄ ⊢ ⬈*[h, o] ⒶVs.W → ⦃G, L⦄ ⊢ ⬈*[h, o] ⒶVs.T →
                      ⦃G, L⦄ ⊢ ⬈*[h, o] ⒶVs.ⓝW.T.
#h #o #G #L #Vs elim Vs -Vs /2 width=1 by csx_cast/
#V #Vs #IHV #W #T #H1W #H1T
lapply (csx_fwd_pair_sn … H1W) #HV
lapply (csx_fwd_flat_dx … H1W) #H2W
lapply (csx_fwd_flat_dx … H1T) #H2T
@csx_appl_simple_theq /2 width=1 by applv_simple, simple_flat/ -IHV -HV -H2W -H2T
#X #H #H0
elim (cpxs_fwd_cast_vector … H) -H #H
[ -H1W -H1T elim H0 -H0 //
| -H1W -H0 /3 width=5 by csx_cpxs_trans, cpxs_flat_dx/
| -H1T -H0 /3 width=5 by csx_cpxs_trans, cpxs_flat_dx/
]
qed.

theorem csx_gcr: ∀h,o. gcr (cpx h o) (eq …) (csx h o) (csx h o).
#h #o @mk_gcr //
[ /3 width=1 by csx_applv_cnx/
|2,3,6: /2 width=1 by csx_applv_beta, csx_applv_sort, csx_applv_cast/
| /2 width=7 by csx_applv_delta/
| #G #L #V1b #V2b #HV12b #a #V #T #H #HV
  @(csx_applv_theta … HV12b) -HV12b
  @csx_abbr //
]
qed.
