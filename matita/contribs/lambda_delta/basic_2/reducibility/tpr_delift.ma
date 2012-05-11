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

include "basic_2/unfold/delift.ma".
include "basic_2/reducibility/tpr_tpss.ma".

(* CONTEXT-FREE PARALLEL REDUCTION ON TERMS *********************************)

(* Properties on inverse basic term relocation ******************************)

lemma tpr_delift_conf: ∀U1,U2. U1 ➡ U2 → ∀L,T1,d,e. L ⊢ U1 [d, e] ≡ T1 →
                       ∃∃T2. T1 ➡ T2 & L ⊢ U2 [d, e] ≡ T2.
#U1 #U2 #HU12 #L #T1 #d #e * #W1 #HUW1 #HTW1
elim (tpr_tpss_conf … HU12 … HUW1) -U1 #U1 #HWU1 #HU21
elim (tpr_inv_lift … HWU1 … HTW1) -W1 /3 width=5/
qed. 