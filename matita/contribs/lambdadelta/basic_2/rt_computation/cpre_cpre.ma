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
include "basic_2/rt_computation/cprs_cprs.ma".
include "basic_2/rt_computation/cpre.ma".

(* EVALUATION FOR CONTEXT-SENSITIVE PARALLEL R-TRANSITION ON TERMS *********)

(* Properties with context-sensitive parallel r-computation for terms ******)

lemma cpre_cprs_conf (h) (G) (L) (T):
      ∀T1. ⦃G,L⦄ ⊢ T ➡*[h] T1 → ∀T2. ⦃G,L⦄ ⊢ T ➡*[h] 𝐍⦃T2⦄ → ⦃G,L⦄ ⊢ T1 ➡*[h] 𝐍⦃T2⦄.
#h #G #L #T0 #T1 #HT01 #T2 * #HT02 #HT2
elim (cprs_conf … HT01 … HT02) -T0 #T0 #HT10 #HT20
lapply (cprs_inv_cnr_sn … HT20 HT2) -HT20 #H destruct
/2 width=1 by conj/
qed-.

(* Main properties *********************************************************)

(* Basic_1: was: nf2_pr3_confluence *)
theorem cpre_mono (h) (G) (L) (T):
        ∀T1. ⦃G,L⦄ ⊢ T ➡*[h] 𝐍⦃T1⦄ → ∀T2. ⦃G,L⦄ ⊢ T ➡*[h] 𝐍⦃T2⦄ → T1 = T2.
#h #G #L #T0 #T1 * #HT01 #HT1 #T2 * #HT02 #HT2
elim (cprs_conf … HT01 … HT02) -T0 #T0 #HT10 #HT20
>(cprs_inv_cnr_sn … HT10 HT1) -T1
>(cprs_inv_cnr_sn … HT20 HT2) -T2 //
qed-.
