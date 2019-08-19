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
include "basic_2/rt_computation/cpre.ma".
include "basic_2/dynamic/cnv_preserve.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

(* Properties with evaluation for t-bound rt-transition on terms ************)

lemma cnv_cpme_trans (a) (h) (n) (G) (L):
      ∀T1. ⦃G,L⦄ ⊢ T1 ![a,h] →
      ∀T2. ⦃G,L⦄ ⊢ T1 ➡*[h,n] 𝐍⦃T2⦄ → ⦃G,L⦄ ⊢ T2 ![a,h].
#a #h #n #G #L #T1 #HT1 #T2 * #HT12 #_
/2 width=4 by cnv_cpms_trans/
qed-.

lemma cnv_cpme_cpms_conf (a) (h) (n) (G) (L):
      ∀T. ⦃G,L⦄ ⊢ T ![a,h] → ∀T1. ⦃G,L⦄ ⊢ T ➡*[n,h] T1 →
      ∀T2. ⦃G,L⦄ ⊢ T ➡*[h,n] 𝐍⦃T2⦄ → ⦃G,L⦄ ⊢ T1 ➡*[h] 𝐍⦃T2⦄.
#a #h #n #G #L #T0 #HT0 #T1 #HT01 #T2 * #HT02 #HT2
elim (cnv_cpms_conf … HT0 … HT01 … HT02) -T0 <minus_n_n #T0 #HT10 #HT20
lapply (cprs_inv_cnr_sn … HT20 HT2) -HT20 #H destruct
/2 width=1 by conj/
qed-.

(* Main properties with evaluation for t-bound rt-transition on terms *****)

theorem cnv_cpme_mono (a) (h) (n) (G) (L):
        ∀T. ⦃G,L⦄ ⊢ T ![a,h] → ∀T1. ⦃G,L⦄ ⊢ T ➡*[h,n] 𝐍⦃T1⦄ →
        ∀T2. ⦃G,L⦄ ⊢ T ➡*[h,n] 𝐍⦃T2⦄ → T1 = T2.
#a #h #n #G #L #T0 #HT0 #T1 * #HT01 #HT1 #T2 * #HT02 #HT2
elim (cnv_cpms_conf … HT0 … HT01 … HT02) -T0 <minus_n_n #T0 #HT10 #HT20
/3 width=7 by cprs_inv_cnr_sn, canc_dx_eq/
qed-.
