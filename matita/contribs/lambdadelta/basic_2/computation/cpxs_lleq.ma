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

include "basic_2/reduction/lpx_leq.ma".
include "basic_2/computation/cpxs.ma".

(* CONTEXT-SENSITIVE EXTENDED PARALLEL COMPUTATION ON TERMS *****************)

(* Properties on lazy equivalence for local environments ********************)

lemma lleq_cpxs_trans: ∀h,g,G,L2,T1,T2. ⦃G, L2⦄ ⊢ T1 ➡*[h, g] T2 →
                       ∀L1. L1 ⋕[0, T1] L2 → ⦃G, L1⦄ ⊢ T1 ➡*[h, g] T2.
#h #g #G #L2 #T1 #T2 #H @(cpxs_ind_dx … H) -T1
/4 width=6 by lleq_cpx_conf_dx, lleq_cpx_trans, cpxs_strap2/
qed-.
