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

include "basic_2/reducibility/tpr_tpr.ma".
include "basic_2/computation/tprs.ma".

(* CONTEXT-FREE PARALLEL COMPUTATION ON TERMS *******************************)

(* Advanced properties ******************************************************)

(* Basic_1: was: pr1_strip *)
lemma tprs_strip: ∀T1,T. T ➡* T1 → ∀T2. T ➡ T2 →
                  ∃∃T0. T1 ➡ T0 & T2 ➡* T0.
/3 width=3 by TC_strip1, tpr_conf/ qed.

(* Main propertis ***********************************************************)

(* Basic_1: was: pr1_confluence *)
theorem tprs_conf: confluent … tprs.
/3 width=3/ qed.

(* Basic_1: was: pr1_t *)
theorem tprs_trans: Transitive … tprs.
/2 width=3/ qed.

(* Basic_1: was: pr1_comp *)
lemma tprs_pair: ∀I,V1,V2. V1 ➡* V2 → ∀T1,T2. T1 ➡* T2 →
                 ②{I} V1. T1 ➡* ②{I} V2. T2.
#I #V1 #V2 #H @(tprs_ind … H) -V2 /2 width=1/
#V #V2 #_ #HV2 #IHV1 #T1 #T2 #HT12
@(tprs_trans … (②{I}V.T2)) /2 width=1/
qed.
