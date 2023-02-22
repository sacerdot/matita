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

include "basic_2/rt_computation/cprs_cnr.ma".
include "basic_2/rt_computation/cprre.ma".
include "basic_2/dynamic/cnv_preserve.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

(* Properties with t-bound evaluation on terms ******************************)

lemma cnv_cpmre_trans (h) (a) (n) (G) (L):
      ∀T1. ❨G,L❩ ⊢ T1 ![h,a] →
      ∀T2. ❨G,L❩ ⊢ T1 ➡*𝐍[h,n] T2 → ❨G,L❩ ⊢ T2 ![h,a].
#h #a #n #G #L #T1 #HT1 #T2 * #HT12 #_
/2 width=4 by cnv_cpms_trans/
qed-.

lemma cnv_cpmre_cpms_conf (h) (a) (n) (G) (L):
      ∀T. ❨G,L❩ ⊢ T ![h,a] → ∀T1. ❨G,L❩ ⊢ T ➡*[h,n] T1 →
      ∀T2. ❨G,L❩ ⊢ T ➡*𝐍[h,n] T2 → ❨G,L❩ ⊢ T1 ➡*𝐍[h,0] T2.
#h #a #n #G #L #T0 #HT0 #T1 #HT01 #T2 * #HT02 #HT2
elim (cnv_cpms_conf … HT0 … HT01 … HT02) -T0 <minus_n_n #T0 #HT10 #HT20
lapply (cprs_inv_cnr_sn … HT20 HT2) -HT20 #H destruct
/2 width=1 by cpmre_intro/
qed-.

(* Main properties with evaluation for t-bound rt-transition on terms *****)

theorem cnv_cpmre_mono (h) (a) (n) (G) (L):
        ∀T. ❨G,L❩ ⊢ T ![h,a] → ∀T1. ❨G,L❩ ⊢ T ➡*𝐍[h,n] T1 →
        ∀T2. ❨G,L❩ ⊢ T ➡*𝐍[h,n] T2 → T1 = T2.
#h #a #n #G #L #T0 #HT0 #T1 * #HT01 #HT1 #T2 * #HT02 #HT2
elim (cnv_cpms_conf … HT0 … HT01 … HT02) -T0 <minus_n_n #T0 #HT10 #HT20
/3 width=7 by cprs_inv_cnr_sn, canc_dx_eq/
qed-.
