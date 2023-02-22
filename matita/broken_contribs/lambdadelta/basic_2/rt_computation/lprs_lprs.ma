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

include "basic_2/rt_computation/cprs_cprs.ma".
include "basic_2/rt_computation/lprs_cpms.ma".

(* PARALLEL R-COMPUTATION FOR FULL LOCAL ENVIRONMENTS ***********************)

(* Main properties **********************************************************)

theorem lprs_trans (h) (G): Transitive … (lprs h 0 G).
/4 width=5 by lprs_cpms_trans, cprs_trans, lex_trans/ qed-.

theorem lprs_conf (h) (G): confluent2 … (lprs h 0 G) (lprs h 0 G).
#h #G #L0 #L1 #HL01 #L2 #HL02
elim (TC_confluent2 … L0 L1 … L2)
[ /3 width=3 by lprs_TC, ex2_intro/ |5,6: skip
| /2 width=1 by lprs_inv_TC/
| /2 width=1 by lprs_inv_TC/
| /2 width=3 by lpr_conf/
]
qed-.
