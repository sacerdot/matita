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

include "static_2/static/reqg_reqg.ma".
include "basic_2/rt_transition/rpx_fsle.ma".

(* EXTENDED CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS **************)

(* Properties with generic equivalence for local environments ***************)

(* Basic_2A1: was just: cpx_lleq_conf_sn *)
lemma cpx_reqg_conf_sn (S) (G):
      s_r_confluent1 … (cpx G) (reqg S).
/3 width=6 by cpx_rex_conf_sn/ qed-.

(* Basic_2A1: was just: cpx_lleq_conf_dx *)
lemma cpx_reqg_conf_dx (S) (G) (L2):
      reflexive … S → symmetric … S →
      ∀T1,T2. ❪G,L2❫ ⊢ T1 ⬈ T2 →
      ∀L1. L1 ≛[S,T1] L2 → L1 ≛[S,T2] L2.
/4 width=4 by cpx_reqg_conf_sn, reqg_sym/ qed-.
