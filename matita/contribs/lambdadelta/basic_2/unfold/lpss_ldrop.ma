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

include "basic_2/substitution/ldrop_lpx_sn.ma".
include "basic_2/unfold/cpss_lift.ma".
include "basic_2/unfold/lpss.ma".

(* SN PARALLEL UNFOLD FOR LOCAL ENVIRONMENTS ********************************)

(* Properies on local environment slicing ***********************************)

lemma lpss_ldrop_conf: dropable_sn lpss.
/3 width=5 by lpx_sn_deliftable_dropable, cpss_inv_lift1/ qed-.

lemma ldrop_lpss_trans: dedropable_sn lpss.
/3 width=9 by lpx_sn_liftable_dedropable, cpss_lift/ qed-.

lemma lpss_ldrop_trans_O1: dropable_dx lpss.
/2 width=3 by lpx_sn_dropable/ qed-.
