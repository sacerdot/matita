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

include "basic_2/static/lfxs_drops.ma".
include "basic_2/rt_transition/cpx_drops.ma".
include "basic_2/rt_transition/lfpx.ma".

(* UNCOUNTED PARALLEL RT-TRANSITION FOR LOCAL ENV.S ON REFERRED ENTRIES *****)

(* Properties with generic slicing for local environments *******************)

lemma drops_lfpx_trans: ∀h,G. dedropable_sn (cpx h G).
/3 width=6 by lfxs_liftable_dedropable, cpx_lifts/ qed-.

(* Inversion lemmas with generic slicing for local environments *************)

lemma lfpx_drops_conf: ∀h,G. dropable_sn (cpx h G).
/2 width=5 by lfxs_dropable_sn/ qed-.

lemma lfpx_drops_trans: ∀h,G. dropable_dx (cpx h G).
/2 width=5 by lfxs_dropable_dx/ qed-.
