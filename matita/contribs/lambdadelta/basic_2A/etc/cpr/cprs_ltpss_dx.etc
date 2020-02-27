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

include "basic_2/reducibility/cpr_ltpss_dx.ma".
include "basic_2/computation/cprs_tpss.ma".

(* CONTEXT-SENSITIVE PARALLEL COMPUTATION ON TERMS **************************)

(* Properties concerning dx partial unfold on local environments ************)

lemma cprs_ltpss_dx_conf: ∀L1,T,U1. L1 ⊢ T ➡* U1 →
                          ∀L2,d,e. L1 ▶* [d, e] L2 →
                          ∃∃U2. L2 ⊢ T ➡* U2 & L2 ⊢ U1 ▶* [d, e] U2.
#L1 #T #U1 #H @(cprs_ind … H) -U1 /2 width=3/
#T1 #U1 #_ #HTU1 #IHT1 #L2 #d #e #HL12
elim (IHT1 … HL12) -IHT1 #U #HTU #HT1U
elim (ltpss_dx_cpr_conf … HTU1 … HL12) -L1 #U0 #HT1U0 #HU10
elim (cpr_tpss_conf … HT1U0 … HT1U) -T1 #U2 #HU02 #HU2
lapply (tpss_trans_eq … HU10 HU02) -U0 /3 width=3/
qed-.

lemma cprs_ltpss_dx_tpss_conf: ∀L1,T1,U1. L1 ⊢ T1 ➡* U1 →
                               ∀L2,d,e. L1 ▶* [d, e] L2 →
                               ∀T2. L2 ⊢ T1 ▶* [d, e] T2 →
                               ∃∃U2. L2 ⊢ T2 ➡* U2 & L2 ⊢ U1 ▶* [d, e] U2.
#L1 #T1 #U1 #HTU1 #L2 #d #e #HL12 #T2 #HT12
elim (cprs_ltpss_dx_conf … HTU1 … HL12) -L1 #U #HT1U #HU1
elim (cprs_tpss_conf … HT1U … HT12) -T1 #T #HUT #HT2
lapply (tpss_trans_eq … HU1 HUT) -U /2 width=3/
qed-.

lemma cprs_ltpss_dx_tpss2_conf: ∀L1,T1,U1. L1 ⊢ T1 ➡* U1 →
                                ∀L2,d,e. L1 ▶* [d, e] L2 →
                                ∀T2. L2 ⊢ T1 ▶* [d, e] T2 →
                                ∀U2. L2 ⊢ U1 ▶* [d, e] U2 →
                                ∃∃U. L2 ⊢ T2 ➡* U & L2 ⊢ U2 ▶* [d, e] U.
#L1 #T1 #U1 #HTU1 #L2 #d #e #HL12 #T2 #HT12 #U2 #HU12
elim (cprs_ltpss_dx_tpss_conf … HTU1 … HL12 … HT12) -L1 -T1 #U #HT2U #HU1
elim (tpss_conf_eq … HU12 … HU1) -U1 #U0 #HU20 #HU0
lapply (cprs_tpss_trans … HT2U … HU0) -U /2 width=3/
qed-.
