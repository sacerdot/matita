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
include "basic_2/unfold/cpqs_lift.ma".
include "basic_2/unfold/lpqs.ma".

(* SN RESTRICTED PARALLEL COMPUTATION FOR LOCAL ENVIRONMENTS ****************)

(* Properies on local environment slicing ***********************************)

lemma lpqs_ldrop_conf: dropable_sn lpqs.
/3 width=5 by lpx_sn_deliftable_dropable, cpqs_inv_lift1/ qed-.

lemma ldrop_lpqs_trans: dedropable_sn lpqs.
/3 width=9 by lpx_sn_liftable_dedropable, cpqs_lift/ qed-.

lemma lpqs_ldrop_trans_O1: dropable_dx lpqs.
/2 width=3 by lpx_sn_dropable/ qed-.
