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

include "static_2/static/reqx_reqx.ma".
include "basic_2/rt_transition/rpx_fsle.ma".

(* UNBOUND CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS ***************)

(* Properties with sort-irrelevant equivalence for local environments *******)

(* Basic_2A1: was just: cpx_lleq_conf_sn *)
lemma cpx_reqx_conf_sn: ∀h,G. s_r_confluent1 … (cpx h G) reqx.
/3 width=6 by cpx_rex_conf/ qed-.

(* Basic_2A1: was just: cpx_lleq_conf_dx *)
lemma cpx_reqx_conf_dx: ∀h,G,L2,T1,T2. ❪G,L2❫ ⊢ T1 ⬈[h] T2 →
                        ∀L1. L1 ≛[T1] L2 → L1 ≛[T2] L2.
/4 width=5 by cpx_reqx_conf_sn, reqx_sym/ qed-.
