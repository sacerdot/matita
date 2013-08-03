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
include "basic_2/reduction/cpx_lift.ma".
include "basic_2/reduction/lpx.ma".

(* SN EXTENDED PARALLEL REDUCTION FOR LOCAL ENVIRONMENTS ********************)

(* Properies on local environment slicing ***********************************)

lemma lpx_ldrop_conf: ∀h,g,G. dropable_sn (lpx h g G).
/3 width=5 by lpx_sn_deliftable_dropable, cpx_inv_lift1/ qed-.

lemma ldrop_lpx_trans: ∀h,g,G. dedropable_sn (lpx h g G).
/3 width=9 by lpx_sn_liftable_dedropable, cpx_lift/ qed-.

lemma lpx_ldrop_trans_O1: ∀h,g,G. dropable_dx (lpx h g G).
/2 width=3 by lpx_sn_dropable/ qed-.
