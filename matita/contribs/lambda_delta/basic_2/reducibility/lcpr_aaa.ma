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

include "basic_2/static/aaa_ltpss_sn.ma".
include "basic_2/reducibility/ltpr_aaa.ma".
include "basic_2/reducibility/cpr.ma".
include "basic_2/reducibility/lcpr.ma".

(* CONTEXT-SENSITIVE PARALLEL REDUCTION ON LOCAL ENVIRONMENTS *************)

(* Properties about atomic arity assignment on terms ************************)

lemma aaa_lcpr_conf: ∀L1,T,A. L1 ⊢ T ⁝ A → ∀L2. L1 ⊢ ➡ L2 → L2 ⊢ T ⁝ A.
#L1 #T #A #HT #L2 * /3 width=5/
qed.

lemma aaa_cpr_conf: ∀L,T1,A. L ⊢ T1 ⁝ A → ∀T2. L ⊢ T1 ➡ T2 → L ⊢ T2 ⁝ A.
#L #T1 #A #HT1 #T2 * /3 width=5/
qed.

lemma aaa_lcpr_cpr_conf: ∀L1,T1,A. L1 ⊢ T1 ⁝ A → ∀L2. L1 ⊢ ➡ L2 →
                         ∀T2. L2 ⊢ T1 ➡ T2 → L2 ⊢ T2 ⁝ A.
/3 width=3/ qed.
