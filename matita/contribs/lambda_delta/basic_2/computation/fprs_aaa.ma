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

include "basic_2/reducibility/cfpr_aaa.ma".
include "basic_2/computation/fprs.ma".

(* CONTEXT-FREE PARALLEL COMPUTATION ON CLOSURES ****************************)

(* Properties about atomic arity assignment on terms ************************)

lemma aaa_fprs_conf: ∀L1,T1,A. L1 ⊢ T1 ⁝ A →
                     ∀L2,T2. ⦃L1, T1⦄ ➡* ⦃L2, T2⦄ → L2 ⊢ T2 ⁝ A.
#L1 #T1 #A #HT1 #L2 #T2 #HLT12
@(bi_TC_Conf3 … HT1 ?? HLT12) /2 width=4/
qed.
