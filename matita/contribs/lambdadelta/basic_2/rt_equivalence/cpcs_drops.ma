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

include "basic_2/rt_equivalence/cpcs_cprs.ma".

(* CONTEXT-SENSITIVE PARALLEL R-EQUIVALENCE FOR TERMS ***********************)

(* Properties with generic slicing for local environments *******************)

(* Basic_1: was: pc3_lift *)
(* Basic_2A1: was: cpcs_lift *)
lemma cpcs_lifts_bi (h) (G): d_liftable2_bi … lifts (cpcs h G).
#h #G #K #T1 #T2 #HT12 #b #f #L #HLK #U1 #HTU1 #U2 #HTU2
elim (cpcs_inv_cprs … HT12) -HT12 #T #HT1 #HT2
elim (lifts_total T f) #U #HU
/3 width=12 by cprs_div, cpms_lifts_bi/
qed-.

(* Inversion lemmas with generic slicing for local environments *************)

(* Basic_1: was: pc3_gen_lift *)
(* Basic_2A1: was cpcs_inv_lift *)
lemma cpcs_inv_lifts_bi (h) (G): d_deliftable2_bi … lifts (cpcs h G).
#h #G #L #U1 #U2 #HU12 #b #f #K #HLK #T1 #HTU1 #T2 #HTU2
elim (cpcs_inv_cprs … HU12) -HU12 #U #HU1 #HU2
elim (cpms_inv_lifts_sn … HU1 … HLK … HTU1) -U1 #T #HTU #HT1
lapply (cpms_inv_lifts_bi … HU2 … HLK … HTU2 … HTU) -L -U -U2 -b -f #HT2
/2 width=3 by cprs_div/
qed-.
