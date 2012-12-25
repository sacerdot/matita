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

include "basic_2/substitution/ldrop_lpx.ma".
include "basic_2/reducibility/tpr_lift.ma".
include "basic_2/reducibility/ltpr.ma".

(* CONTEXT-FREE PARALLEL REDUCTION ON LOCAL ENVIRONMENTS ********************)

(* Basic_1: was: wcpr0_drop *)
lemma ltpr_ldrop_conf: dropable_sn ltpr.
/3 width=3 by lpx_deliftable_dropable, tpr_inv_lift1/ qed.

(* Basic_1: was: wcpr0_drop_back *)
lemma ldrop_ltpr_trans: dedropable_sn ltpr.
/2 width=3/ qed.

lemma ltpr_ldrop_trans_O1: dropable_dx ltpr.
/2 width=3/ qed.
