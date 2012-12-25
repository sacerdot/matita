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

include "basic_2/reducibility/ltpr_tps.ma".
include "basic_2/reducibility/cpr_ltpss.ma".
include "basic_2/reducibility/lfpr.ma".
include "basic_2/computation/cprs.ma".

(* CONTEXT-SENSITIVE PARALLEL COMPUTATION ON TERMS **************************)

(* Properties concerning focalized parallel reduction on local environments *)

lemma ltpr_tpss_trans: ∀L1,L2. L1 ➡ L2 → ∀T1,T2,d,e. L2 ⊢ T1 ▶* [d, e] T2 →
                       ∃∃T. L1 ⊢ T1 ▶* [d, e] T & L1 ⊢ T ➡* T2.
#L1 #L2 #HL12 #T1 #T2 #d #e #H @(tpss_ind … H) -T2
[ /2 width=3/
| #T #T2 #_ #HT2 * #T0 #HT10 #HT0
  elim (ltpr_tps_trans … HT2 … HL12) -L2 #T3 #HT3 #HT32
  @(ex2_1_intro … HT10) -T1 (**) (* explicit constructors *)
  @(cprs_strap1 … T3 …) /2 width=1/ -HT32
  @(cprs_strap1 … HT0) -HT0 /3 width=3/
]
qed.

(* Basic_1: was just: pr3_pr0_pr2_t *)
lemma ltpr_cpr_trans: ∀L1,L2. L1 ➡ L2 → ∀T1,T2. L2 ⊢ T1 ➡ T2 → L1 ⊢ T1 ➡* T2.
#L1 #L2 #HL12 #T1 #T2 * #T #HT1
<(ltpr_fwd_length … HL12) #HT2
elim (ltpr_tpss_trans … HL12 … HT2) -L2 /3 width=3/
qed.

(* Basic_1: was just: pr3_pr2_pr2_t *)
lemma lfpr_cpr_trans: ∀L1,L2. ⦃L1⦄ ➡ ⦃L2⦄ → ∀T1,T2. L2 ⊢ T1 ➡ T2 → L1 ⊢ T1 ➡* T2.
#L1 #L2 * /3 width=7/
qed.
