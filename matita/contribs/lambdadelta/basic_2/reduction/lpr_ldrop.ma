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

include "basic_2/relocation/ldrop_lpx_sn.ma".
include "basic_2/reduction/cpr_lift.ma".
include "basic_2/reduction/lpr.ma".

(* SN PARALLEL REDUCTION FOR LOCAL ENVIRONMENTS *****************************)

(* Properies on local environment slicing ***********************************)

(* Basic_1: includes: wcpr0_drop *)
lemma lpr_ldrop_conf: dropable_sn lpr.
/3 width=5 by lpx_sn_deliftable_dropable, cpr_inv_lift1/ qed-.

(* Basic_1: includes: wcpr0_drop_back *)
lemma ldrop_lpr_trans: dedropable_sn lpr.
/3 width=9 by lpx_sn_liftable_dedropable, cpr_lift/ qed-.

lemma lpr_ldrop_trans_O1: dropable_dx lpr.
/2 width=3 by lpx_sn_dropable/ qed-.
