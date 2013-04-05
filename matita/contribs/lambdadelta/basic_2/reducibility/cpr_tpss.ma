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

include "basic_2/reducibility/ltpr_tpss.ma".
include "basic_2/reducibility/cpr.ma".

(* CONTEXT-SENSITIVE PARALLEL REDUCTION ON TERMS ****************************)

(* Properties on partial unfold for terms ***********************************)

lemma cpr_tpss_trans: ∀L,T1,T. L ⊢ T1 ➡ T →
                      ∀T2,d,e. L ⊢ T ▶* [d, e] T2 → L ⊢ T1 ➡ T2.
#L #T1 #T * #T0 #HT10 #HT0 #T2 #d #e #HT2
lapply (tpss_weak_full … HT2) -HT2 #HT2
lapply (tpss_trans_eq … HT0 HT2) -T /2 width=3/
qed.

lemma cpr_tps_trans: ∀L,T1,T. L ⊢ T1 ➡ T →
                     ∀T2,d,e. L ⊢ T ▶ [d, e] T2 → L ⊢ T1 ➡ T2.
/3 width=5/ qed.

lemma cpr_tpss_conf: ∀L,T0,T1. L ⊢ T0 ➡ T1 →
                     ∀T2,d,e. L ⊢ T0 ▶* [d, e] T2 →
                     ∃∃T. L ⊢ T1 ▶* [d, e] T & L ⊢ T2 ➡ T.
#L #T0 #T1 * #U0 #HTU0 #HU0T1 #T2 #d #e #HT02
elim (tpr_tpss_conf … HTU0 … HT02) -T0 #T0 #HT20 #HUT0
elim (tpss_conf_eq … HU0T1 … HUT0) -U0 /3 width=5/
qed-.
