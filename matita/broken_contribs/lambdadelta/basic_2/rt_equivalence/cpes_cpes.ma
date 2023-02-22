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

include "basic_2/rt_computation/lprs_cpms.ma".
include "basic_2/rt_equivalence/cpes_cpms.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL RT-EQUIVALENCE FOR TERMS **************)

(* Advanced forward lemmas **************************************************)

lemma cpes_fwd_abst_bi (h) (n1) (n2) (p1) (p2) (G) (L):
      ∀W1,W2,T1,T2. ❨G,L❩ ⊢ ⓛ[p1]W1.T1 ⬌*[h,n1,n2] ⓛ[p2]W2.T2 →
      ∧∧ p1 = p2 & ❨G,L❩ ⊢ W1 ⬌*[h,0,O] W2.
#h #n1 #n2 #p1 #p2 #G #L #W1 #W2 #T1 #T2 * #X #H1 #H2
elim (cpms_inv_abst_sn … H1) #W0 #X0 #HW10 #_ #H destruct
elim (cpms_inv_abst_bi … H2) #H #HW20 #_ destruct
/3 width=3 by cpms_div, conj/
qed-.

(* Main properties **********************************************************)

theorem cpes_cpes_trans (h) (n1) (n2) (G) (L) (T):
        ∀T1. ❨G,L❩ ⊢ T ⬌*[h,n1,0] T1 →
        ∀T2. ❨G,L❩ ⊢ T1 ⬌*[h,0,n2] T2 → ❨G,L❩ ⊢ T ⬌*[h,n1,n2] T2.
#h #n1 #n2 #G #L #T #T1 #HT1 #T2 * #X #HX1 #HX2
lapply (cpes_cprs_trans … HT1 … HX1) -T1 #HTX
lapply (cpes_cpms_div … HTX … HX2) -X //
qed-.
