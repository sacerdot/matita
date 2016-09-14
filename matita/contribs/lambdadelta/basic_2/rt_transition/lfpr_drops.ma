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
include "basic_2/rt_transition/cpm_drops.ma".
include "basic_2/rt_transition/lfpr.ma".

(* PARALLEL R-TRANSITION FOR LOCAL ENV.S ON REFERRED ENTRIES ****************)

(* Properties with generic slicing for local environments *******************)

lemma drops_lfpr_trans: ∀h,G. dedropable_sn (cpm 0 h G).
/3 width=6 by lfxs_liftable_dedropable, cpm_lifts/ qed-.

(* Inversion lemmas with generic slicing for local environments *************)

lemma lfpr_drops_conf: ∀h,G. dropable_sn (cpm 0 h G).
/2 width=5 by lfxs_dropable_sn/ qed-.

lemma lfpr_drops_trans: ∀h,G. dropable_dx (cpm 0 h G).
/2 width=5 by lfxs_dropable_dx/ qed-.
