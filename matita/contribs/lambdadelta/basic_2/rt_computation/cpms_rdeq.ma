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

include "basic_2/rt_computation/cpxs_rdeq.ma".
include "basic_2/rt_computation/cpms_cpxs.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL RT-COMPUTATION FOR TERMS **************)

(* Properties with sort-irrelevant equivalence for local environments *******)

lemma cpms_rdeq_conf_sn (h) (n) (G) (L1) (L2):
                        ∀T1,T2. ⦃G,L1⦄ ⊢ T1 ➡*[n,h] T2 →
                        L1 ≛[T1] L2 → L1 ≛[T2] L2.
/3 width=5 by cpms_fwd_cpxs, cpxs_rdeq_conf_sn/ qed-.

lemma cpms_rdeq_conf_dx (h) (n) (G) (L1) (L2):
                        ∀T1,T2. ⦃G,L2⦄ ⊢ T1 ➡*[n,h] T2 →
                        L1 ≛[T1] L2 → L1 ≛[T2] L2.
/3 width=5 by cpms_fwd_cpxs, cpxs_rdeq_conf_dx/ qed-.
