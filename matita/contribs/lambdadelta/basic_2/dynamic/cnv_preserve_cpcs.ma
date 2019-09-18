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

include "basic_2/rt_equivalence/cpcs_cprs.ma".
include "basic_2/dynamic/cnv_preserve.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

(* Forward lemmas with r-equivalence ****************************************)

lemma cnv_cpms_conf_eq (h) (a) (n) (G) (L):
      ∀T. ⦃G,L⦄ ⊢ T ![h,a] →
      ∀T1. ⦃G,L⦄ ⊢ T ➡*[n,h] T1 → ∀T2. ⦃G,L⦄ ⊢ T ➡*[n,h] T2 → ⦃G,L⦄ ⊢ T1 ⬌*[h] T2.
#h #a #n #G #L #T #HT #T1 #HT1 #T2 #HT2
elim (cnv_cpms_conf … HT … HT1 … HT2) -T <minus_n_n #T #HT1 #HT2
/2 width=3 by cprs_div/
qed-.

lemma cnv_cpms_fwd_appl_sn_decompose (h) (a) (G) (L):
      ∀V,T. ⦃G,L⦄ ⊢ ⓐV.T ![h,a] → ∀n,X. ⦃G,L⦄ ⊢ ⓐV.T ➡*[n,h] X →
      ∃∃U. ⦃G,L⦄ ⊢ T ![h,a] & ⦃G,L⦄ ⊢ T ➡*[n,h] U & ⦃G,L⦄ ⊢ ⓐV.U ⬌*[h] X.
#h #a #G #L #V #T #H0 #n #X #HX
elim (cnv_inv_appl … H0) #m #p #W #U #_ #_ #HT #_ #_ -m -p -W -U
elim (cnv_fwd_cpms_total h … n … HT) #U #HTU
lapply (cpms_appl_dx … V V … HTU) [ // ] #H
/3 width=8 by cnv_cpms_conf_eq, ex3_intro/
qed-.
