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

include "basic_2/unfold/tpss_tpss.ma".
include "basic_2/reducibility/cpr.ma".

(* CONTEXT-SENSITIVE PARALLEL REDUCTION ON TERMS ****************************)

(* Properties on partial unfold for terms ***********************************)

lemma cpr_tpss_trans: ∀L,T1,T. L ⊢ T1 ➡ T →
                      ∀T2. L ⊢ T ▶* [O, |L|] T2 → L ⊢ T1 ➡ T2.
#L #T1 #T * #T0 #HT10 #HT0 #T2 #HT2
lapply (tpss_trans_eq … HT0 HT2) -T /2 width=3/
qed.

lemma cpr_tps_trans: ∀L,T1,T. L ⊢ T1 ➡ T →
                     ∀T2. L ⊢ T ▶ [O, |L|] T2 → L ⊢ T1 ➡ T2.
/3 width=3/ qed.
