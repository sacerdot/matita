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

include "basic_2/static/lfdeq.ma".
include "basic_2/rt_transition/cpx_lfxs.ma".

(* UNCOUNTED CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS *************)

(* Properties with degree-based equivalence for local environments **********)

(* Basic_2A1: was just: cpx_lleq_conf_sn *)
lemma cpx_lfdeq_conf_sn: ∀h,o,G. s_r_confluent1 … (cpx h G) (lfdeq h o).
/3 width=6 by cpx_lfxs_conf/ qed-.

(* Basic_2A1: was just: cpx_lleq_conf_dx *)
lemma cpx_lfdeq_conf_dx: ∀h,o,G,L2,T1,T2. ⦃G, L2⦄ ⊢ T1 ⬈[h] T2 →
                         ∀L1. L1 ≡[h, o, T1] L2 → L1 ≡[h, o, T2] L2.
/4 width=4 by cpx_lfdeq_conf_sn, lfdeq_sym/ qed-.
