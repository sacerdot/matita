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

include "basic_2/rt_computation/cpms_cnu.ma".
include "basic_2/rt_computation/cpue.ma".
include "basic_2/dynamic/cnv_preserve.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

(* Properties with evaluation for t-unbound rt-transition on terms **********)

lemma cnv_cpue_trans (a) (h) (G) (L):
      ∀T1. ⦃G,L⦄ ⊢ T1 ![a,h] →
      ∀T2. ⦃G,L⦄ ⊢ T1 ⥲*[h] 𝐍⦃T2⦄ → ⦃G,L⦄ ⊢ T2 ![a,h].
#a #h #G #L #T1 #HT1 #T2 * #n #HT12 #_
/2 width=4 by cnv_cpms_trans/
qed-.

lemma cnv_cpue_cpms_conf (a) (h) (n) (G) (L):
      ∀T0. ⦃G,L⦄ ⊢ T0 ![a,h] → ∀T1. ⦃G,L⦄ ⊢ T0 ➡*[n,h] T1 →
      ∀T2. ⦃G,L⦄ ⊢ T0 ⥲*[h] 𝐍⦃T2⦄ →
      ∃∃T. ⦃G,L⦄ ⊢ T1 ⥲*[h] 𝐍⦃T⦄ & T2 ≅ T.
#a #h #n1 #G #L #T0 #HT0 #T1 #HT01 #T2 * #n2 #HT02 #HT2
elim (cnv_cpms_conf … HT0 … HT01 … HT02) -T0 #T0 #HT10 #HT20
lapply (cpms_inv_cnu_sn … HT20 HT2) -HT20 #HT20
/4 width=8 by cnu_tueq_trans, ex2_intro/
qed-.

(* Main properties with evaluation for t-unbound rt-transition on terms *****)

theorem cnv_cpue_mono (a) (h) (G) (L):
        ∀T0. ⦃G,L⦄ ⊢ T0 ![a,h] → ∀T1. ⦃G,L⦄ ⊢ T0 ⥲*[h] 𝐍⦃T1⦄ →
        ∀T2. ⦃G,L⦄ ⊢ T0 ⥲*[h] 𝐍⦃T2⦄ → T1 ≅ T2.
#a #h #G #L #T0 #HT0 #T1 * #n1 #HT01 #HT1 #T2 * #n2 #HT02 #HT2
elim (cnv_cpms_conf … HT0 … HT01 … HT02) -T0 #T0 #HT10 #HT20
/3 width=8 by cpms_inv_cnu_sn, tueq_canc_dx/
qed-.
