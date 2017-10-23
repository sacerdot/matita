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

(* Basic_2A1: uses: drop_lpx_trans *) 
lemma drops_lfpx_trans: ∀h,G. dedropable_sn (cpx h G).
/3 width=6 by lfxs_liftable_dedropable_sn, cpx_lifts_sn/ qed-.

(* Inversion lemmas with generic slicing for local environments *************)

(* Basic_2A1: uses: lpx_drop_conf *)
lemma lfpx_drops_conf: ∀h,G. dropable_sn (cpx h G).
/2 width=5 by lfxs_dropable_sn/ qed-.

(* Basic_2A1: uses: lpx_drop_trans_O1 *)
lemma lfpx_drops_trans: ∀h,G. dropable_dx (cpx h G).
/2 width=5 by lfxs_dropable_dx/ qed-.

lemma lfpx_inv_lref_pair_sn: ∀h,G,L1,L2,i. ⦃G, L1⦄ ⊢ ⬈[h, #i] L2 → ∀I,K1,V1. ⬇*[i] L1 ≡ K1.ⓑ{I}V1 →
                             ∃∃K2,V2. ⬇*[i] L2 ≡ K2.ⓑ{I}V2 & ⦃G, K1⦄ ⊢ ⬈[h, V1] K2 & ⦃G, K1⦄ ⊢ V1 ⬈[h] V2.
/2 width=3 by lfxs_inv_lref_pair_sn/ qed-.

lemma lfpx_inv_lref_pair_dx: ∀h,G,L1,L2,i. ⦃G, L1⦄ ⊢ ⬈[h, #i] L2 → ∀I,K2,V2. ⬇*[i] L2 ≡ K2.ⓑ{I}V2 →
                             ∃∃K1,V1. ⬇*[i] L1 ≡ K1.ⓑ{I}V1 & ⦃G, K1⦄ ⊢ ⬈[h, V1] K2 & ⦃G, K1⦄ ⊢ V1 ⬈[h] V2.
/2 width=3 by lfxs_inv_lref_pair_dx/ qed-.
