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

include "basic_2/i_static/tc_lfxs_drops.ma".
include "basic_2/rt_transition/lfpx_drops.ma".

(* UNCOUNTED PARALLEL RT-COMPUTATION FOR LOCAL ENV.S ON REFERRED ENTRIES ****)

(* Properties with generic slicing for local environments *******************)

(* Basic_2A1: uses: drop_lpxs_trans *)
lemma drops_lfpxs_trans: ∀h,G. tc_dedropable_sn (cpx h G).
/3 width=5 by drops_lfpx_trans, dedropable_sn_CTC/ qed-.

(* Inversion lemmas with generic slicing for local environments *************)

(* Basic_2A1: uses: lpxs_drop_conf *)
lemma lfpxs_drops_conf: ∀h,G. tc_dropable_sn (cpx h G).
/3 width=5 by lfpx_drops_conf, dropable_sn_CTC/ qed-.

(* Basic_2A1: uses: lpxs_drop_trans_O1 *)
lemma lfpxs_drops_trans: ∀h,G. tc_dropable_dx (cpx h G).
/3 width=5 by lfpx_drops_trans, dropable_dx_CTC/ qed-.
