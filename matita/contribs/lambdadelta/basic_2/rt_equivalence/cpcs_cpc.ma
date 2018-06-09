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

include "basic_2/rt_conversion/cpc_cpc.ma".
include "basic_2/rt_equivalence/cpcs.ma".

(* CONTEXT-SENSITIVE PARALLEL R-EQUIVALENCE FOR TERMS ***********************)

(* Properties with context-sensitive parallel r-conversion for terms ********)

lemma cpcs_strip (h) (G) (L): confluent2 … (cpcs h G L) (cpc h G L).
#h #G #L #T1 #T @TC_strip1 /2 width=3 by cpc_conf/
qed-.
