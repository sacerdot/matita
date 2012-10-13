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
include "basic_2/reducibility/lfpr.ma".

(* FOCALIZED PARALLEL REDUCTION FOR LOCAL ENVIRONMENTS **********************)

(* Properties about atomic arity assignment on terms ************************)

lemma aaa_lfpr_conf: ∀L1,T,A. L1 ⊢ T ⁝ A → ∀L2. ⦃L1⦄ ➡ ⦃L2⦄ → L2 ⊢ T ⁝ A.
#L1 #T #A #HT #L2 * /3 width=5/
qed.
