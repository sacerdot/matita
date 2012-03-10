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
(*
include "basic_2/reducibility/cpr_lift.ma".
include "basic_2/reducibility/lcpr_cpr.ma".
*)
include "basic_2/computation/cprs_cprs.ma".

(* CONTEXT-SENSITIVE PARALLEL COMPUTATION ON TERMS **************************)

(* Forward lemmas involving same top term constructor ***********************)
(*
lemma cpr_fwd_beta: ∀L,V,W,T,U. L ⊢ ⓐV. ⓛW. T ➡ U →
                    ⓐV. ⓛW. T ≃ U ∨ L ⊢ ⓓV. T ➡* U.
#L #V #W #T #U #H
elim (cpr_inv_appl1 … H) -H *
[ #V0 #X #_ #_ #H destruct /2 width=1/
| #V0 #W0 #T1 #T2 #HV0 #HT12 #H1 #H2 destruct
  lapply (lcpr_cpr_trans (L. ⓓV) … HT12) -HT12 /2 width=1/ /3 width=1/
| #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #H destruct
]
qed-.

lemma cpr_fwd_theta: ∀L,V1,V,T,U. L ⊢ ⓐV1. ⓓV. T ➡ U →
                     ∀V2. ⇧[0, 1] V1 ≡ V2 → ⓐV1. ⓓV. T ≃ U ∨
                     L ⊢ ⓓV. ⓐV2. T ➡* U.
#L #V1 #V #T #U #H #V2 #HV12
elim (cpr_inv_appl1 … H) -H *
[ -HV12 #V0 #X #_ #_ #H destruct /2 width=1/
| -HV12 #V0 #W #T1 #T2 #_ #_ #H destruct
| #V0 #V3 #W1 #W2 #T1 #T2 #HV10 #HW12 #HT12 #HV03 #H1 #H2 destruct
  lapply (cpr_lift (L.ⓓW1) … HV12 … HV03 … HV10) -V0 -HV12 /2 width=1/ #HV23
  lapply (lcpr_cpr_trans (L. ⓓW1) … HT12) -HT12 /2 width=1/ #HT12
  /4 width=1/
]
qed-.
*)
lemma cprs_fwd_tau: ∀L,W,T,U. L ⊢ ⓣW. T ➡* U →
                    ⓣW. T ≃ U ∨ L ⊢ T ➡* U.
#L #W #T #U #H
elim (cprs_inv_cast1 … H) -H /2 width=1/ *
#W0 #T0 #_ #_ #H destruct /2 width=1/
qed-.
