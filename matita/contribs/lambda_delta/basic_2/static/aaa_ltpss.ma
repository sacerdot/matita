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

include "basic_2/unfold/ltpss.ma".
include "basic_2/static/aaa_ltps.ma".

(* ATONIC ARITY ASSIGNMENT ON TERMS *****************************************)

(* Properties about parallel unfold *****************************************)

lemma aaa_ltpss_conf: ∀L1,T,A. L1 ⊢ T ÷ A → ∀L2,d,e. L1 [d, e] ▶* L2 → L2 ⊢ T ÷ A.
#L1 #T #A #HT #L2 #d #e #HL12
@(TC_Conf3 … (λL,A. L ⊢ T ÷ A) … HT ? HL12) /2 width=5/
qed.

lemma aaa_tpss_conf: ∀L,T1,A. L ⊢ T1 ÷ A → ∀T2,d,e. L ⊢ T1 [d, e] ▶* T2 → L ⊢ T2 ÷ A.
#L #T1 #A #HT1 #T2 #d #e #HT12
@(TC_Conf3 … HT1 ? HT12) /2 width=5/
qed.

lemma aaa_ltpss_tpss_conf: ∀L1,T1,A. L1 ⊢ T1 ÷ A → ∀L2,d,e. L1 [d, e] ▶* L2 →
                           ∀T2. L2 ⊢ T1 [d, e] ▶* T2 → L2 ⊢ T2 ÷ A.
/3 width=5/ qed.
