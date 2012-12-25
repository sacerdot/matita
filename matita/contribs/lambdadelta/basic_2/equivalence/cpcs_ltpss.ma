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

include "basic_2/equivalence/cpcs_cpcs.ma".

(* CONTEXT-SENSITIVE PARALLEL EQUIVALENCE ON TERMS **************************)

(* Properties concerning partial unfold on local environments ***************)

lemma ltpss_dx_cpr_conf: ∀L1,L2,d,e. L1 ▶* [d, e] L2 →
                         ∀T1,T2. L1 ⊢ T1 ➡ T2 → L2 ⊢ T1 ⬌* T2.
#L1 #L2 #d #e #HL12 #T1 #T2 *
lapply (ltpss_dx_weak_all … HL12)
>(ltpss_dx_fwd_length … HL12) -HL12 #HL12 #T #HT1 #HT2
elim (ltpss_dx_tpss_conf … HT2 … HL12) -L1 #T0 #HT0 #HT20
@(cprs_div … T0) /3 width=3/ (**) (* /4/ is too slow *)
qed.

lemma ltpss_dx_cprs_conf: ∀L1,L2,d,e. L1 ▶* [d, e] L2 →
                          ∀T1,T2. L1 ⊢ T1 ➡* T2 → L2 ⊢ T1 ⬌* T2.
#L1 #L2 #d #e #HL12 #T1 #T2 #H @(cprs_ind … H) -T2 //
#T #T2 #_ #HT2 #IHT1
@(cpcs_trans … IHT1) -T1 /2 width=5/
qed.

lemma ltpss_dx_cpcs_conf: ∀L1,L2,d,e. L1 ▶* [d, e] L2 →
                          ∀T1,T2. L1 ⊢ T1 ⬌* T2 → L2 ⊢ T1 ⬌* T2.
#L1 #L2 #d #e #HL12 #T1 #T2 #H
elim (cpcs_inv_cprs … H) -H #T #HT1 #HT2
@(cpcs_canc_dx … T) /2 width=5/
qed.
