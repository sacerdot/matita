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

include "basic_2/reducibility/lfpr_aaa.ma".
include "basic_2/computation/lfprs.ma".

(* FOCALIZED PARALLEL COMPUTATION ON LOCAL ENVIRONMENTS *********************)

(* Properties about atomic arity assignment on terms ************************)

lemma aaa_lfprs_conf: ∀L1,T,A. L1 ⊢ T ⁝ A → ∀L2. ⦃L1⦄ ➡* ⦃L2⦄ → L2 ⊢ T ⁝ A.
#L1 #T #A #HT #L2 #HL12
@(TC_Conf3 … (λL,A. L ⊢ T ⁝ A) … HT ? HL12) /2 width=3/
qed.
(*
(* Note: this should be rephrased in terms of fprs *)
lemma aaa_lfprs_cprs_conf: ∀L1,T1,A. L1 ⊢ T1 ⁝ A → ∀L2. ⦃L1⦄ ➡* ⦃L2⦄ →
                           ∀T2. L2 ⊢ T1 ➡* T2 → L2 ⊢ T2 ⁝ A.
/3 width=3/ qed.
*)
