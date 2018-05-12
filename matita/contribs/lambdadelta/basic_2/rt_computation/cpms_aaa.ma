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

include "basic_2/rt_computation/cpxs_aaa.ma".
include "basic_2/rt_computation/cpms_cpxs.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL RT-COMPUTATION FOR TERMS **************)

(* Properties with atomic arity assignment on terms *************************)

(* Basic_2A1: uses: scpds_aaa_conf *)
(* Basic_2A1: includes: cprs_aaa_conf *)
lemma cpms_aaa_conf (n) (h): ∀G,L. Conf3 … (aaa G L) (cpms h G L n).
/3 width=5 by cpms_fwd_cpxs, cpxs_aaa_conf/ qed-.
