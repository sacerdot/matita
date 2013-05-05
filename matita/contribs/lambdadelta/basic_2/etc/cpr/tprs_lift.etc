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

include "basic_2/reducibility/tpr_lift.ma".
include "basic_2/computation/tprs.ma".

(* CONTEXT-FREE PARALLEL COMPUTATION ON TERMS *******************************)

(* Advanced inversion lemmas ************************************************)

lemma tprs_inv_abst1: ∀a,V1,T1,U2. ⓛ{a}V1. T1 ➡* U2 →
                      ∃∃V2,T2. V1 ➡* V2 & T1 ➡* T2 & U2 = ⓛ{a}V2. T2.
#a #V1 #T1 #U2 #H @(tprs_ind … H) -U2 /2 width=5/
#U #U2 #_ #HU2 * #V #T #HV1 #HT1 #H destruct
elim (tpr_inv_abst1 … HU2) -HU2 #V2 #T2 #HV2 #HT2 #H destruct /3 width=5/
qed-.

lemma tprs_inv_abst: ∀a,V1,V2,T1,T2. ⓛ{a}V1. T1 ➡* ⓛ{a}V2. T2 →
                     V1 ➡* V2 ∧ T1 ➡* T2.
#a #V1 #V2 #T1 #T2 #H
elim (tprs_inv_abst1 … H) -H #V #T #HV1 #HT1 #H destruct /2 width=1/
qed-.

(* Relocation properties ****************************************************)

(* Note: this was missing in basic_1 *)
lemma tprs_lift: t_liftable tprs.
/3 width=7/ qed.

(* Note: this was missing in basic_1 *)
lemma tprs_inv_lift1: t_deliftable_sn tprs.
/3 width=3 by tpr_inv_lift1, t_deliftable_sn_TC/ qed-.
