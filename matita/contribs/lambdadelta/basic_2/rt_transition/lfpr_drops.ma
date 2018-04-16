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

(* Basic_2A1: uses: drop_lpr_trans *)
lemma drops_lfpr_trans: ∀h,G. dedropable_sn (cpm 0 h G).
/3 width=6 by lfxs_liftable_dedropable_sn, cpm_lifts_sn/ qed-.

(* Inversion lemmas with generic slicing for local environments *************)

(* Basic_2A1: uses: lpr_drop_conf *)
lemma lfpr_drops_conf: ∀h,G. dropable_sn (cpm 0 h G).
/2 width=5 by lfxs_dropable_sn/ qed-.

(* Basic_2A1: uses: lpr_drop_trans_O1 *)
lemma lfpr_drops_trans: ∀h,G. dropable_dx (cpm 0 h G).
/2 width=5 by lfxs_dropable_dx/ qed-.

lemma lfpr_inv_lref_pair_sn: ∀h,G,L1,L2,i. ⦃G, L1⦄ ⊢ ➡[h, #i] L2 → ∀I,K1,V1. ⬇*[i] L1 ≘ K1.ⓑ{I}V1 →
                             ∃∃K2,V2. ⬇*[i] L2 ≘ K2.ⓑ{I}V2 & ⦃G, K1⦄ ⊢ ➡[h, V1] K2 & ⦃G, K1⦄ ⊢ V1 ➡[h] V2.
/2 width=3 by lfxs_inv_lref_pair_sn/ qed-.

lemma lfpr_inv_lref_pair_dx: ∀h,G,L1,L2,i. ⦃G, L1⦄ ⊢ ➡[h, #i] L2 → ∀I,K2,V2. ⬇*[i] L2 ≘ K2.ⓑ{I}V2 →
                             ∃∃K1,V1. ⬇*[i] L1 ≘ K1.ⓑ{I}V1 & ⦃G, K1⦄ ⊢ ➡[h, V1] K2 & ⦃G, K1⦄ ⊢ V1 ➡[h] V2.
/2 width=3 by lfxs_inv_lref_pair_dx/ qed-.
