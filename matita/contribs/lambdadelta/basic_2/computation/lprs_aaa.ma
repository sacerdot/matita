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

include "basic_2/reduction/lpx_aaa.ma".
include "basic_2/computation/lprs.ma".

(* SN PARALLEL COMPUTATION ON LOCAL ENVIRONMENTS ****************************)

(* Properties about atomic arity assignment on terms ************************)

lemma aaa_lprs_conf: ∀L1,T,A. L1 ⊢ T ⁝ A → ∀L2. L1 ⊢ ➡* L2 → L2 ⊢ T ⁝ A.
#L1 #T #A #HT #L2 #HL12
@(TC_Conf3 … (λL,A. L ⊢ T ⁝ A) … HT ? HL12) /2 width=3 by aaa_lpr_conf/
qed-.
