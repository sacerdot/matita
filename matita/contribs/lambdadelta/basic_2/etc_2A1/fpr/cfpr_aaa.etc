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

include "basic_2/reducibility/cpr_aaa.ma".
include "basic_2/reducibility/cfpr_cpr.ma".

(* CONTEXT-SENSITIVE PARALLEL REDUCTION ON CLOSURES *************************)

(* Properties about atomic arity assignment on terms ************************)

lemma aaa_fpr_conf: ∀L1,T1,A. L1 ⊢ T1 ⁝ A →
                    ∀L2,T2. ⦃L1, T1⦄ ➡ ⦃L2, T2⦄ → L2 ⊢ T2 ⁝ A.
#L1 #T1 #A #HT1 #L2 #T2 #H
elim (fpr_inv_all … H) -H
/4 width=5 by aaa_cpr_conf, aaa_ltpr_conf, aaa_ltpss_sn_conf/
qed.
