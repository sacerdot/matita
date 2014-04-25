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

include "basic_2/reduction/cpx_lleq.ma".
include "basic_2/computation/cpxs.ma".

(* CONTEXT-SENSITIVE EXTENDED PARALLEL COMPUTATION ON TERMS *****************)

(* Properties on lazy equivalence for local environments ********************)

lemma lleq_cpxs_trans: ∀h,g,G,L2,T1,T2. ⦃G, L2⦄ ⊢ T1 ➡*[h, g] T2 →
                       ∀L1. L1 ≡[T1, 0] L2 → ⦃G, L1⦄ ⊢ T1 ➡*[h, g] T2.
#h #g #G #L2 #T1 #T2 #H @(cpxs_ind_dx … H) -T1
/4 width=6 by cpx_lleq_conf_dx, lleq_cpx_trans, cpxs_strap2/
qed-.

lemma cpxs_lleq_conf: ∀h,g,G,L2,T1,T2. ⦃G, L2⦄ ⊢ T1 ➡*[h, g] T2 →
                      ∀L1. L2 ≡[T1, 0] L1 → ⦃G, L1⦄ ⊢ T1 ➡*[h, g] T2.
/3 width=3 by lleq_cpxs_trans, lleq_sym/ qed-.

lemma cpxs_lleq_conf_dx: ∀h,g,G,L2,T1,T2. ⦃G, L2⦄ ⊢ T1 ➡*[h, g] T2 →
                         ∀L1. L1 ≡[T1, 0] L2 → L1 ≡[T2, 0] L2.
#h #g #G #L2 #T1 #T2 #H @(cpxs_ind … H) -T2 /3 width=6 by cpx_lleq_conf_dx/
qed-.

lemma cpxs_lleq_conf_sn: ∀h,g,G,L1,T1,T2. ⦃G, L1⦄ ⊢ T1 ➡*[h, g] T2 →
                         ∀L2. L1 ≡[T1, 0] L2 → L1 ≡[T2, 0] L2.
/4 width=6 by cpxs_lleq_conf_dx, lleq_sym/ qed-.
