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

include "basic_2/reduction/lpr_aaa.ma".
include "basic_2/computation/cprs.ma".

(* CONTEXT-SENSITIVE PARALLEL COMPUTATION ON TERMS **************************)

(* Properties about atomic arity assignment on terms ************************)

lemma aaa_cprs_conf: ∀L,T1,A. L ⊢ T1 ⁝ A → ∀T2. L ⊢ T1 ➡* T2 → L ⊢ T2 ⁝ A.
#L #T1 #A #HT1 #T2 #HT12
@(TC_Conf3 … HT1 ? HT12) -A -T1 -T2 /2 width=3 by aaa_cpr_conf/
qed-.
