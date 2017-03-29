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

include "basic_2/relocation/drops.ma".

(* GENERIC SLICING FOR LOCAL ENVIRONMENTS ***********************************)

(* Properties with context-sensitive equivalence for terms ******************)

lemma ceq_lift_sn: d_liftable2_sn ceq.
/2 width=3 by ex2_intro/ qed-.

lemma ceq_inv_lift_sn: d_deliftable2_sn ceq.
/2 width=3 by ex2_intro/ qed-.

(* Note: d_deliftable2_sn cfull does not hold *)
lemma cfull_lift_sn: d_liftable2_sn cfull.
#K #T1 #T2 #_ #b #f #L #_ #U1 #_ -K -T1 -b
elim (lifts_total T2 f) /2 width=3 by ex2_intro/
qed-.
