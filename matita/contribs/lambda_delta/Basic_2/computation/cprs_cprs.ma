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

include "Basic_2/reducibility/cpr_cpr.ma".
include "Basic_2/computation/cprs_lcpr.ma".

(* CONTEXT-SENSITIVE PARALLEL COMPUTATION ON TERMS **************************)

(* Main propertis ***********************************************************)

(* Basic_1: was: pr3_t *)
theorem cprs_trans: ∀L,T1,T. L ⊢ T1 ➡* T → ∀T2. L ⊢ T ➡* T2 → L ⊢ T1 ➡* T2.
/2 width=3/ qed.

(* Basic_1: was: pr3_confluence *)
theorem cprs_conf: ∀L,T1,T. L ⊢ T ➡* T1 → ∀T2. L ⊢ T ➡* T2 →
                   ∃∃T0. L ⊢ T1 ➡* T0 & L ⊢ T2 ➡* T0.
/3 width=3/ qed.

(* Advanced properties ******************************************************)

(* Basic_1: was only: pr3_pr2_pr3_t *)
lemma lcpr_cprs_trans: ∀L1,L2. L1 ⊢ ➡ L2 →
                       ∀T1,T2. L2 ⊢ T1 ➡* T2 → L1 ⊢ T1 ➡* T2.
#L1 #L2 #HL12 #T1 #T2 #H @(cprs_ind … H) -T2 //
#T #T2 #_ #HT2 #IHT2 /3 width=5/
qed.

lemma cpr_abbr: ∀L,V1,V2. L ⊢ V1 ➡ V2 → ∀T1,T2. L. ⓓV1 ⊢ T1 ➡ T2 →
                L ⊢ ⓓV1. T1 ➡* ⓓV2. T2.
#L #V1 #V2 #HV12 #T1 #T2 #HT12
@(cprs_strap2 … (ⓓV1.T2)) /2 width=1/ /3 width=1/
qed.
