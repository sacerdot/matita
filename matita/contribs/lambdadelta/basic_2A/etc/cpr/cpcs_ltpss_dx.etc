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

include "basic_2/computation/cprs_ltpss_dx.ma".
include "basic_2/equivalence/cpcs_cpcs.ma".

(* CONTEXT-SENSITIVE PARALLEL EQUIVALENCE ON TERMS **************************)

(* Properties concerning dx partial unfold on local environments ************)

lemma cpcs_ltpss_dx_conf: ∀L1,L2,d,e. L1 ▶* [d, e] L2 →
                          ∀T1,T2. L1 ⊢ T1 ⬌* T2 → L2 ⊢ T1 ⬌* T2.
#L1 #L2 #d #e #HL12 #T1 #T2 #H
elim (cpcs_inv_cprs … H) -H #T #HT1 #HT2
elim (cprs_ltpss_dx_conf … HT1 … HL12) -HT1 #U1 #HTU1 #H1
elim (cprs_ltpss_dx_conf … HT2 … HL12) -L1 #U2 #HTU2 #H2
elim (tpss_conf_eq … H1 … H2) -T #U #HU1 #HU2
lapply (cprs_tpss_trans … HTU1 … HU1) -U1
lapply (cprs_tpss_trans … HTU2 … HU2) -U2 /2 width=3/
qed-.

lemma cpcs_ltpss_dx_tpss_conf: ∀L1,L2,d,e. L1 ▶* [d, e] L2 →
                               ∀T,T2. L1 ⊢ T ⬌* T2 →
                               ∀T1. L2 ⊢ T ▶* [d, e] T1 →
                               L2 ⊢ T1 ⬌* T2.
#L1 #L2 #d #e #HL12 #T #T2 #HT2 #T1 #HT1
lapply (cpcs_ltpss_dx_conf … HL12 … HT2) -L1 #HT2
lapply (cpcs_tpss_conf … HT1 … HT2) -T //
qed-.

lemma cpcs_ltpss_dx_tpss2_conf: ∀L1,L2,d,e. L1 ▶* [d, e] L2 →
                                ∀T1,T2. L1 ⊢ T1 ⬌* T2 →
                                ∀T3. L2 ⊢ T1 ▶* [d, e] T3 →
                                ∀T4. L2 ⊢ T2 ▶* [d, e] T4 →
                                L2 ⊢ T3 ⬌* T4.
#L1 #L2 #d #e #HL12 #T1 #T2 #HT12 #T3 #HT13 #T4 #HT24
lapply (cpcs_ltpss_dx_tpss_conf … HL12 … HT12 … HT13) -L1 -T1 #HT32
lapply (cpcs_tpss_strap1 … HT32 … HT24) -T2 //
qed-.
