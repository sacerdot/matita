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

include "basic_2/relocation/lifts_tdeq.ma".
include "basic_2/static/lfxs_drops.ma".
include "basic_2/static/lfdeq.ma".

(* DEGREE-BASED EQUIVALENCE FOR LOCAL ENVIRONMENTS ON REFERRED ENTRIES ******)

(* Properties with generic slicing for local environments *******************)

lemma lfdeq_lifts_sn: ∀h,o. dedropable_sn (cdeq h o).
/3 width=5 by lfxs_liftable_dedropable_sn, tdeq_lifts_sn/ qed-.

(* Inversion lemmas with generic slicing for local environments *************)

lemma lfdeq_inv_lifts_sn: ∀h,o. dropable_sn (cdeq h o).
/2 width=5 by lfxs_dropable_sn/ qed-.

(* Note: missing in basic_2A1 *)
lemma lfdeq_inv_lifts_dx: ∀h,o. dropable_dx (cdeq h o).
/2 width=5 by lfxs_dropable_dx/ qed-.

(* Basic_2A1: uses: lleq_inv_lift_le lleq_inv_lift_be lleq_inv_lift_ge *)
lemma lfdeq_inv_lifts_bi: ∀h,o,L1,L2,U. L1 ≡[h, o, U] L2 → ∀b,f. 𝐔⦃f⦄ →
                          ∀K1,K2. ⬇*[b, f] L1 ≡ K1 → ⬇*[b, f] L2 ≡ K2 →
                          ∀T. ⬆*[f] T ≡ U → K1 ≡[h, o, T] K2.
/2 width=10 by lfxs_inv_lifts_bi/ qed-.

lemma lfdeq_inv_lref_pair_sn: ∀h,o,L1,L2,i. L1 ≡[h, o, #i] L2 → ∀I,K1,V1. ⬇*[i] L1 ≡ K1.ⓑ{I}V1 →
                              ∃∃K2,V2. ⬇*[i] L2 ≡ K2.ⓑ{I}V2 & K1 ≡[h, o, V1] K2 & V1 ≡[h, o] V2.
/2 width=3 by lfxs_inv_lref_pair_sn/ qed-.

lemma lfdeq_inv_lref_pair_dx: ∀h,o,L1,L2,i. L1 ≡[h, o, #i] L2 → ∀I,K2,V2. ⬇*[i] L2 ≡ K2.ⓑ{I}V2 →
                              ∃∃K1,V1. ⬇*[i] L1 ≡ K1.ⓑ{I}V1 & K1 ≡[h, o, V1] K2 & V1 ≡[h, o] V2.
/2 width=3 by lfxs_inv_lref_pair_dx/ qed-.
