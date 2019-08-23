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

include "basic_2/rt_computation/cprs_cprs.ma".
include "basic_2/rt_equivalence/cpes.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL RT-EQUIVALENCE FOR TERMS **************)

(* Properties with t-bound rt-computation on terms **************************)

lemma cpes_cprs_trans (h) (n) (G) (L) (T0):
      ∀T1.  ⦃G,L⦄ ⊢ T1 ⬌*[h,n,0] T0 →
      ∀T2.  ⦃G,L⦄ ⊢ T0 ➡*[h] T2 → ⦃G,L⦄ ⊢ T1 ⬌*[h,n,0] T2.
#h #n #G #L #T0 #T1 * #T #HT1 #HT0 #T2 #HT02
elim (cprs_conf … HT0 … HT02) -T0 #T0 #HT0 #HT20
/3 width=3 by cpms_div, cpms_cprs_trans/
qed-.

lemma cpes_cpms_div (h) (n) (n1) (n2) (G) (L) (T0):
      ∀T1.  ⦃G,L⦄ ⊢ T1 ⬌*[h,n,n1] T0 →
      ∀T2.  ⦃G,L⦄ ⊢ T2 ➡*[n2,h] T0 → ⦃G,L⦄ ⊢ T1 ⬌*[h,n,n2+n1] T2.
#h #n #n1 #n2 #G #L #T0 #T1 * #T #HT1 #HT0 #T2 #HT20
lapply (cpms_trans … HT20 … HT0) -T0 #HT2
/2 width=3 by cpms_div/
qed-.
