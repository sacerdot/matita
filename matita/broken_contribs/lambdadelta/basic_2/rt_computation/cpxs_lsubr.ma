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

include "basic_2/rt_transition/cpx_lsubr.ma".
include "basic_2/rt_computation/cpxs.ma".

(* EXTENDED CONTEXT-SENSITIVE PARALLEL RT-COMPUTATION FOR TERMS *************)

(* Properties with restricted refinement for local environments *************)

lemma lsubr_cpxs_trans (G): lsub_trans … (cpxs G) lsubr.
/3 width=5 by lsubr_cpx_trans, CTC_lsub_trans/
qed-.
