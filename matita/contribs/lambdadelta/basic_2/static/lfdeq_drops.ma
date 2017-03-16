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
include "basic_2/static/lfdeq_fqup.ma".

(* DEGREE-BASED EQUIVALENCE FOR LOCAL ENVIRONMENTS ON REFERRED ENTRIES ******)

(* Properties with generic slicing for local environments *******************)

(* Basic_2A1: includes: lleq_lift_le lleq_lift_ge *)
lemma lfdeq_lifts: ∀h,o. dedropable_sn (cdeq h o).
/3 width=5 by lfxs_liftable_dedropable, tdeq_lifts/ qed-.

(* Inversion lemmas with generic slicing for local environments *************)

(* Basic_2A1: restricts: lleq_inv_lift_le lleq_inv_lift_be lleq_inv_lift_ge *)
lemma lfdeq_inv_lifts: ∀h,o. dropable_sn (cdeq h o).
/2 width=5 by lfxs_dropable_sn/ qed-.

(* Note: missing in basic_2A1 *)
lemma lfdeq_inv_lifts_dx: ∀h,o. dropable_dx (cdeq h o).
/2 width=5 by lfxs_dropable_dx/ qed-.

(* Note: missing in basic_2A1 *)
lemma lfdeq_inv_lifts_bi: ∀h,o,L1,L2,U. L1 ≡[h, o, U] L2 →
                          ∀K1,K2,i. ⬇*[i] L1 ≡ K1 → ⬇*[i] L2 ≡ K2 →
                          ∀T. ⬆*[i] T ≡ U → K1 ≡[h, o, T] K2.
/2 width=8 by lfxs_inv_lifts_bi/ qed-.

lemma lfdeq_inv_lref_sn: ∀h,o,L1,L2,i. L1 ≡[h, o, #i] L2 → ∀I,K1,V1. ⬇*[i] L1 ≡ K1.ⓑ{I}V1 →
                         ∃∃K2,V2. ⬇*[i] L2 ≡ K2.ⓑ{I}V2 & K1 ≡[h, o, V1] K2 & V1 ≡[h, o] V2.
/2 width=3 by lfxs_inv_lref_sn/ qed-.

lemma lfdeq_inv_lref_dx: ∀h,o,L1,L2,i. L1 ≡[h, o, #i] L2 → ∀I,K2,V2. ⬇*[i] L2 ≡ K2.ⓑ{I}V2 →
                         ∃∃K1,V1. ⬇*[i] L1 ≡ K1.ⓑ{I}V1 & K1 ≡[h, o, V1] K2 & V1 ≡[h, o] V2.
/2 width=3 by lfxs_inv_lref_dx/ qed-.
