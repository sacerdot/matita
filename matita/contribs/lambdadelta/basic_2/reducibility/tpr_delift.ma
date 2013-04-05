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
include "basic_2/reducibility/ltpr_tpss.ma".

(* CONTEXT-FREE PARALLEL REDUCTION ON TERMS *********************************)

(* Properties on inverse basic term relocation ******************************)

lemma tpr_delift_conf: ∀U1,U2. U1 ➡ U2 → ∀L,T1,d,e. L ⊢ ▼*[d, e] U1 ≡ T1 →
                       ∃∃T2. T1 ➡ T2 & L ⊢ ▼*[d, e] U2 ≡ T2.
#U1 #U2 #HU12 #L #T1 #d #e * #W1 #HUW1 #HTW1
elim (tpr_tpss_conf … HU12 … HUW1) -U1 #U1 #HWU1 #HU21
elim (tpr_inv_lift1 … HWU1 … HTW1) -W1 /3 width=5/
qed-.
