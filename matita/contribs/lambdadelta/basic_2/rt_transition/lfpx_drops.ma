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

include "basic_2/substitution/lpx_sn_drop.ma".
include "basic_2/rt_transition/cpx_drops.ma".
include "basic_2/rt_transition/lfpx.ma".

(* UNCOUNTED PARALLEL RT-TRANSITION FOR LOCAL ENV.S ON REFERRED ENTRIES *****)

(* Properties on local environment slicing ***********************************)

lemma lpx_drop_conf: ∀h,o,G. dropable_sn (lpx h o G).
/3 width=6 by lpx_sn_deliftable_dropable, cpx_inv_lift1/ qed-.

lemma drop_lpx_trans: ∀h,o,G. dedropable_sn (lpx h o G).
/3 width=10 by lpx_sn_liftable_dedropable, cpx_lift/ qed-.

lemma lpx_drop_trans_O1: ∀h,o,G. dropable_dx (lpx h o G).
/2 width=3 by lpx_sn_dropable/ qed-.
