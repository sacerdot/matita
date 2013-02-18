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

include "basic_2/unfold/ltpss_dx_ltpss_dx.ma".
include "basic_2/reducibility/cpr.ma".

(* CONTEXT-SENSITIVE PARALLEL REDUCTION ON TERMS ****************************)

(* Properties concerning dx partial unfold on local environments ************)

lemma ltpss_dx_cpr_conf: ∀L1,T,U1. L1 ⊢ T ➡ U1 →
                         ∀L2,d,e. L1 ▶* [d, e] L2 →
                         ∃∃U2. L2 ⊢ T ➡ U2 & L2 ⊢ U1 ▶* [d, e] U2.
#L1 #T #U1 * #U #HTU #HU1 #L2 #d #e #HL12
lapply (ltpss_dx_fwd_length … HL12) #H >H in HU1; -H #HU1
elim (ltpss_dx_tpss_conf … HU1 … HL12) -L1 /3 width=3/
qed-.
