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

include "basic_2/unfold/ltpss_sn_ltpss_sn.ma".
include "basic_2/reducibility/cpr.ma".

(* CONTEXT-SENSITIVE PARALLEL REDUCTION ON TERMS ****************************)

(* Properties concerning partial unfold on local environments ***************)

lemma ltpss_sn_cpr_trans: ∀L1,L2,d,e. L1 ⊢ ▶* [d, e] L2 →
                          ∀T1,T2. L2 ⊢ T1 ➡ T2 → L1 ⊢ T1 ➡ T2.
#L1 #L2 #d #e #HL12 #T1 #T2 *
lapply (ltpss_sn_weak_all … HL12)
<(ltpss_sn_fwd_length … HL12) -HL12 /3 width=5/
qed.