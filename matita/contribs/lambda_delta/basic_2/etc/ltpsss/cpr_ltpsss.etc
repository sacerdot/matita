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

include "basic_2/unfold/ltpsss.ma".
include "basic_2/reducibility/cpr_ltpss.ma".

(* CONTEXT-SENSITIVE PARALLEL REDUCTION ON TERMS ****************************)

(* Properties on iterated partial unfold on local environments **************)

lemma ltpsss_cpr_trans: ∀L1,L2,d,e. L1 [d, e] ▶** L2 →
                        ∀T1,T2. L2 ⊢ T1 ➡ T2 → L1 ⊢ T1 ➡ T2.
#L1 #L2 #d #e #HL12 #T1 #T2 #HT12 @(ltpsss_ind_dx … HL12) -L1 // /2 width=5/
qed.
