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

include "basic_2/rt_computation/cpms_lsubr.ma".
include "basic_2/rt_equivalence/cpcs_cprs.ma".

(* CONTEXT-SENSITIVE PARALLEL R-EQUIVALENCE FOR TERMS ***********************)

(* Properties with restricted refinement for local environments *************)

lemma lsubr_cpcs_trans (h) (G): lsub_trans … (cpcs h G) lsubr.
#h #G #L1 #T1 #T2 #HT12 elim (cpcs_inv_cprs … HT12) -HT12
/3 width=5 by cprs_div, lsubr_cpms_trans/
qed-.
