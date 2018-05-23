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

include "basic_2/rt_transition/cpm_cpx.ma".
include "basic_2/rt_transition/lpx_aaa.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS ***************)

(* Properties with atomic arity assignment for terms ************************)

(* Basic_2A1: includes: cpr_aaa_conf *)
lemma cpm_aaa_conf (n) (h): ∀G,L. Conf3 … (aaa G L) (cpm h G L n).
/3 width=5 by cpx_aaa_conf, cpm_fwd_cpx/ qed-.
