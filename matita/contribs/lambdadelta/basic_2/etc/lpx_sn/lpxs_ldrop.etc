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

include "basic_2/reduction/lpx_ldrop.ma".
include "basic_2/computation/lpxs.ma".

(* SN EXTENDED PARALLEL COMPUTATION ON LOCAL ENVIRONMENTS *******************)

(* Properies on local environment slicing ***********************************)

lemma lpxs_ldrop_conf: ∀h,g,G. dropable_sn (lpxs h g G).
/3 width=3 by dropable_sn_TC, lpx_ldrop_conf/ qed-.

lemma ldrop_lpxs_trans: ∀h,g,G. dedropable_sn (lpxs h g G).
/3 width=3 by dedropable_sn_TC, ldrop_lpx_trans/ qed-.

lemma lpxs_ldrop_trans_O1: ∀h,g,G. dropable_dx (lpxs h g G).
/3 width=3 by dropable_dx_TC, lpx_ldrop_trans_O1/ qed-.
