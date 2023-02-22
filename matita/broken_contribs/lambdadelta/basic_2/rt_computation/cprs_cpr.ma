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

include "basic_2/rt_transition/cpr_cpr.ma".
include "basic_2/rt_computation/cprs_ctc.ma".

(* CONTEXT-SENSITIVE PARALLEL R-COMPUTATION FOR TERMS ***********************)

(* Advanced properties with context-sensitive r-transition for terms ********)

(* Basic_1: was: pr3_strip *)
(* Basic_1: includes: pr1_strip *)
lemma cprs_strip (h) (G) (L): confluent2 … (cpms h G L 0) (cpm h G L 0).
#h #G #L #T0 #T1 #HT01 #T2 #HT02
elim (TC_strip1 … T0 T1 … HT02) -HT02
[ /3 width=3 by cprs_CTC, ex2_intro/ | skip
| /2 width=1 by cprs_inv_CTC/
| /2 width=3 by cpr_conf/
]
qed-.
