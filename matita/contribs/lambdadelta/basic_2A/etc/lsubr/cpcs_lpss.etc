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

include "basic_2/computation/cprs_lpss.ma".
include "basic_2/equivalence/cpcs_cpcs.ma".

(* CONTEXT-SENSITIVE PARALLEL EQUIVALENCE ON TERMS **************************)

(* Properties on sn parallel substitution for local environments ************)

lemma cpcs_lpss_conf: ∀L1,T1,T2. L1 ⊢ T1 ⬌* T2 →
                      ∀L2. L1 ⊢ ▶* L2 → L2 ⊢ T1 ⬌* T2.
#L1 #T1 #T2 #H #L2 #HL12
elim (cpcs_inv_cprs … H) -H #T #HT1 #HT2
elim (cprs_lpss_conf_dx … HT1 … HL12) -HT1 #U1 #H1 #HTU1
elim (cprs_lpss_conf_dx … HT2 … HL12) -L1 #U2 #H2 #HTU2
elim (cpss_conf … H1 … H2) -T #U #HU1 #HU2
lapply (cprs_cpss_trans … HTU1 … HU1) -U1
lapply (cprs_cpss_trans … HTU2 … HU2) -U2 /2 width=3/
qed-.

lemma cpcs_cpss_lpss_conf: ∀L1,T,T2. L1 ⊢ T ⬌* T2 → ∀T1. L1 ⊢ T ▶* T1 →
                           ∀L2. L1 ⊢ ▶* L2 → L2 ⊢ T1 ⬌* T2.
#L1 #T #T2 #HT2 #T1 #HT1 #L2 #HL12
lapply (cpcs_lpss_conf … HT2 … HL12) -HT2 #HT2
elim (lpss_cpss_conf_dx … HT1 … HL12) -L1 #T0 #HT0 #HT10
lapply (cpcs_cpss_conf … HT0 … HT2) -T #HT02
lapply (cpcs_cpss_strap2 … HT10 … HT02) -T0 //
qed-.

lemma cpcs_cpss2_lpss_conf: ∀L1,T1,T2. L1 ⊢ T1 ⬌* T2 →
                            ∀T3. L1 ⊢ T1 ▶* T3 → ∀T4. L1 ⊢ T2 ▶* T4 →
                            ∀L2. L1 ⊢ ▶* L2 → L2 ⊢ T3 ⬌* T4.
#L1 #T1 #T2 #HT12 #T3 #HT13 #T4 #HT24 #L2 #HL12
lapply (cpcs_cpss_lpss_conf … HT12 … HT13 … HL12) -T1 #HT32
elim (lpss_cpss_conf_dx … HT24 … HL12) -L1 #T #HT2 #HT4
lapply (cpcs_cpss_strap1 … HT32 … HT2) -T2 #HT3
lapply (cpcs_cpss_div … HT3 … HT4) -T //
qed-.
