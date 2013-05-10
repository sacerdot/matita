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

include "basic_2/substitution/lpss_lpss.ma".
include "basic_2/computation/cprs_lpss.ma".
include "basic_2/equivalence/cpcs_cpcs.ma".

(* CONTEXT-SENSITIVE PARALLEL EQUIVALENCE ON TERMS **************************)

(* Properties on sn parallel substitution for local environments ************)

lemma cpcs_lpss_conf: ∀L1,L2. L1 ⊢ ▶* L2 → ∀T1,T2. L1 ⊢ T1 ⬌* T2 → L2 ⊢ T1 ⬌* T2.
#L1 #L2 #HL12 #T1 #T2 #H
elim (cpcs_inv_cprs … H) -H #T #HT1 #HT2
elim (cprs_lpss_conf_dx … HT1 … HL12) -HT1 #U1 #H1 #HTU1
elim (cprs_lpss_conf_dx … HT2 … HL12) -L1 #U2 #H2 #HTU2
elim (cpss_conf … H1 … H2) -T #U #HU1 #HU2
lapply (cprs_cpss_trans … HTU1 … HU1) -U1
lapply (cprs_cpss_trans … HTU2 … HU2) -U2 /2 width=3/
qed-.

lemma cpcs_lpss_cpss_conf: ∀L1,L2. L1 ⊢ ▶* L2 →
                           ∀T,T2. L1 ⊢ T ⬌* T2 →
                           ∀T1. L2 ⊢ T ▶* T1 →
                           L2 ⊢ T1 ⬌* T2.
#L1 #L2 #HL12 #T #T2 #HT2 #T1 #HT1
lapply (cpcs_lpss_conf … HL12 … HT2) -L1 #HT2
lapply (cpcs_cpss_conf … HT1 … HT2) -T //
qed-.

lemma cpcs_lpss_cpss2_conf: ∀L1,L2. L1 ⊢ ▶* L2 → ∀T1,T2. L1 ⊢ T1 ⬌* T2 →
                            ∀T3. L2 ⊢ T1 ▶* T3 → ∀T4. L2 ⊢ T2 ▶* T4 →
                            L2 ⊢ T3 ⬌* T4.
#L1 #L2 #HL12 #T1 #T2 #HT12 #T3 #HT13 #T4 #HT24
lapply (cpcs_lpss_cpss_conf … HL12 … HT12 … HT13) -L1 -T1 #HT32
lapply (cpcs_cpss_strap1 … HT32 … HT24) -T2 //
qed-.
