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

(* Properties concerning parallel unfold on terms ***************************)

(* Note: we could invoke tpss_weak_full instead of ltpr_fwd_length *)
(* Basic_1: was only: pr2_subst1 *)
lemma cpr_tpss_ltpr: ∀L1,L2. L1 ➡ L2 → ∀T1,T2. L2 ⊢ T1 ➡ T2 →
                     ∀d,e,U1. L1 ⊢ T1 ▶* [d, e] U1 →
                     ∃∃U2. L2 ⊢ U1 ➡ U2 & L2 ⊢ T2 ▶* [d, e] U2.
#L1 #L2 #HL12 #T1 #T2 * #T #HT1 #HT2 #d #e #U1 #HTU1
elim (ltpr_tpr_tpss_conf … HL12 … HT1 … HTU1) -L1 -HT1 #U #HU1 #HTU
elim (tpss_conf_eq … HT2 … HTU) -T /3 width=3/
qed.

lemma cpr_ltpr_conf_eq: ∀L1,T1,T2. L1 ⊢ T1 ➡ T2 → ∀L2. L1 ➡ L2 →
                        ∃∃T. L2 ⊢ T1 ➡ T & T2 ➡ T.
#L1 #T1 #T2 * #T #HT1 #HT2 #L2 #HL12
>(ltpr_fwd_length … HL12) in HT2; #HT2
elim (ltpr_tpr_tpss_conf … HL12 … HT2) -L1 /3 width=3/
qed.

lemma cpr_ltpr_conf_tpss: ∀L1,L2. L1 ➡ L2 → ∀T1,T2. L1 ⊢ T1 ➡ T2 →
                          ∀d,e,U1. L1 ⊢ T1 ▶* [d, e] U1 →
                          ∃∃U2. L2 ⊢ U1 ➡ U2 & L2 ⊢ T2 ➡ U2.
#L1 #L2 #HL12 #T1 #T2 #HT12 #d #e #U1 #HTU1
elim (cpr_ltpr_conf_eq … HT12 … HL12) -HT12 #T #HT1 #HT2
elim (cpr_tpss_ltpr … HL12 … HT1 … HTU1) -L1 -HT1 #U2 #HU12 #HTU2
lapply (tpss_weak_full … HTU2) -HTU2 #HTU2 /3 width=5/ (**) (* /4 width=5/ is too slow *)
qed.
