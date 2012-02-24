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

include "Basic_2/substitution/lift_vector.ma".
include "Basic_2/computation/cprs_tstc.ma".

(* CONTEXT-SENSITIVE PARALLEL COMPUTATION ON TERMS **************************)

(* Vector form of forward lemmas involving same top term constructor ********)

lemma cpr_fwd_theta_vector: ∀L,V1s,V2s. ⇧[0, 1] V1s ≡ V2s →
                            ∀V,T,U. L ⊢ ⒶV1s. ⓓV. T ➡ U →
                            ⒶV1s. ⓓV. T ≃ U ∨ L ⊢ ⓓV. ⒶV2s. T ➡* U.
#L #V1s #V2s * -V1s -V2s /3 width=1/
#V1s #V2s #V1a #V2a #HV12a * -V1s -V2s /2 width=1 by cpr_fwd_theta/ -HV12a
#V1s #V2s #V1b #V2b #_ #_ #V #U #T #H
elim (cpr_inv_appl1_simple … H ?) -H //
#V0 #T0 #_ #_ #H destruct /2 width=1/
qed-.

axiom cprs_fwd_theta_vector: ∀L,V1s,V2s. ⇧[0, 1] V1s ≡ V2s →
                            ∀V,T,U. L ⊢ ⒶV1s. ⓓV. T ➡* U →
                            ⒶV1s. ⓓV. T ≃ U ∨ L ⊢ ⓓV. ⒶV2s. T ➡* U.