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

include "basic_2/reduction/lpx_drop.ma".
include "basic_2/computation/lpxs.ma".

(* SN EXTENDED PARALLEL COMPUTATION ON LOCAL ENVIRONMENTS *******************)

(* Properties on local environment slicing ***********************************)

lemma lpxs_drop_conf: ∀h,g,G. dropable_sn (lpxs h g G).
/3 width=3 by dropable_sn_TC, lpx_drop_conf/ qed-.

lemma drop_lpxs_trans: ∀h,g,G. dedropable_sn (lpxs h g G).
/3 width=3 by dedropable_sn_TC, drop_lpx_trans/ qed-.

lemma lpxs_drop_trans_O1: ∀h,g,G. dropable_dx (lpxs h g G).
/3 width=3 by dropable_dx_TC, lpx_drop_trans_O1/ qed-.
