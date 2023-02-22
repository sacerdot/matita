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

include "basic_2/rt_transition/cpx_reqg.ma".
include "basic_2/rt_computation/cpxs_teqg.ma".

(* EXTENDED CONTEXT-SENSITIVE PARALLEL RT-COMPUTATION FOR TERMS *************)

(* Properties with generic equivalence for local environments ***************)

(* Basic_2A1: was just: lleq_cpxs_trans *)
lemma reqg_cpxs_trans (S) (G):
      reflexive … S → symmetric … S →
      ∀L0,T0,T1. ❨G,L0❩ ⊢ T0 ⬈* T1 → ∀L2. L2 ≛[S,T0] L0 → ❨G,L2❩ ⊢ T0 ⬈* T1.
#S #G #H1S #H2S #L0 #T0 #T1 #H @(cpxs_ind_dx … H) -T0 //
#T0 #T #H0T0 #_ #IH #L2 #HL2
lapply (reqg_cpx_trans … HL2 … H0T0) // #H2T0
lapply (IH L2 ?) -IH /2 width=5 by cpx_reqg_conf_dx/ -L0 #H2T1
/2 width=3 by cpxs_strap2/
qed-.

(* Basic_2A1: was just: cpxs_lleq_conf *)
lemma cpxs_reqg_conf (S) (G):
      reflexive … S → symmetric … S →
      ∀L0,T0,T1. ❨G,L0❩ ⊢ T0 ⬈* T1 → ∀L2. L0 ≛[S,T0] L2 → ❨G,L2❩ ⊢ T0 ⬈* T1.
/3 width=8 by reqg_cpxs_trans, reqg_sym/ qed-.

(* Basic_2A1: was just: lleq_conf_sn *)
lemma cpxs_reqg_conf_sn (S) (G):
      ∀L1,T1,T2. ❨G,L1❩ ⊢ T1 ⬈* T2 →
      ∀L2. L1 ≛[S,T1] L2 → L1 ≛[S,T2] L2.
#S #G #L1 #T1 #T2 #H @(cpxs_ind … H) -T2
/3 width=6 by cpx_reqg_conf_sn/
qed-.

(* Basic_2A1: was just: cpxs_lleq_conf_dx *)
lemma cpxs_reqg_conf_dx (S) (G):
      reflexive … S → symmetric … S →
      ∀L2,T1,T2. ❨G,L2❩ ⊢ T1 ⬈* T2 →
      ∀L1. L1 ≛[S,T1] L2 → L1 ≛[S,T2] L2.
/4 width=4 by cpxs_reqg_conf_sn, reqg_sym/ qed-.
