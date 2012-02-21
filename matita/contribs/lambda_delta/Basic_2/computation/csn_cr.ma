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

include "Basic_2/computation/acp_cr.ma".
include "Basic_2/computation/csn_lcpr.ma".
include "Basic_2/computation/csn_vector.ma".

(* CONTEXT-SENSITIVE STRONGLY NORMALIZING TERMS *****************************)

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

lemma csn_applv_theta: ∀L,V1s,V2s. ⇧[0, 1] V1s ≡ V2s →
                       ∀V,T. L ⊢ ⬇* ⓓV. ⒶV2s. T → L ⊢ ⬇* V → L ⊢ ⬇* ⒶV1s. ⓓV. T.
#L #V1s #V2s * -V1s -V2s /2 width=1/
#V1s #V2s #V1 #V2 #HV12 * -V1s -V2s /2 width=3/
#V1s #V2s #W1 #W2 #HW12 #HV12s #V #T #H #HV
lapply (csn_appl_theta … HV12 … H) -H -HV12 #H
lapply (csn_fwd_pair_sn … H) #HV1
@csn_appl_simple // #X #H1 #H2
whd in ⊢ (? ? %);
*)
(*
lemma csn_S5: ∀L,V1s,V2s. ⇧[0, 1] V1s ≡ V2s →
              ∀V,T. L. ⓓV ⊢ ⬇* ⒶV2s. T → L ⊢ ⬇* V → L ⊢ ⬇* ⒶV1s. ⓓV. T.
#L #V1s #V2s #H elim H -V1s -V2s /2 width=1/
*)

axiom csn_acr: acr cpr (eq …) (csn …) (λL,T. L ⊢ ⬇* T).
