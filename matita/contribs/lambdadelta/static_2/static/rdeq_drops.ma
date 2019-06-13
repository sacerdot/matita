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

include "static_2/relocation/lifts_tdeq.ma".
include "static_2/static/rex_drops.ma".
include "static_2/static/rdeq.ma".

(* SORT-IRRELEVANT EQUIVALENCE FOR LOCAL ENVIRONMENTS ON REFERRED ENTRIES ***)

(* Properties with generic slicing for local environments *******************)

lemma rdeq_lifts_sn: f_dedropable_sn cdeq.
/3 width=5 by rex_liftable_dedropable_sn, tdeq_lifts_sn/ qed-.

(* Inversion lemmas with generic slicing for local environments *************)

lemma rdeq_inv_lifts_sn: f_dropable_sn cdeq.
/2 width=5 by rex_dropable_sn/ qed-.

lemma rdeq_inv_lifts_dx: f_dropable_dx cdeq.
/2 width=5 by rex_dropable_dx/ qed-.

lemma rdeq_inv_lifts_bi: ∀L1,L2,U. L1 ≛[U] L2 → ∀b,f. 𝐔⦃f⦄ →
                         ∀K1,K2. ⬇*[b,f] L1 ≘ K1 → ⬇*[b,f] L2 ≘ K2 →
                         ∀T. ⬆*[f] T ≘ U → K1 ≛[T] K2.
/2 width=10 by rex_inv_lifts_bi/ qed-.

lemma rdeq_inv_lref_pair_sn: ∀L1,L2,i. L1 ≛[#i] L2 → ∀I,K1,V1. ⬇*[i] L1 ≘ K1.ⓑ{I}V1 →
                             ∃∃K2,V2. ⬇*[i] L2 ≘ K2.ⓑ{I}V2 & K1 ≛[V1] K2 & V1 ≛ V2.
/2 width=3 by rex_inv_lref_pair_sn/ qed-.

lemma rdeq_inv_lref_pair_dx: ∀L1,L2,i. L1 ≛[#i] L2 → ∀I,K2,V2. ⬇*[i] L2 ≘ K2.ⓑ{I}V2 →
                             ∃∃K1,V1. ⬇*[i] L1 ≘ K1.ⓑ{I}V1 & K1 ≛[V1] K2 & V1 ≛ V2.
/2 width=3 by rex_inv_lref_pair_dx/ qed-.

lemma rdeq_inv_lref_pair_bi (L1) (L2) (i):
                            L1 ≛[#i] L2 →
                            ∀I1,K1,V1. ⬇*[i] L1 ≘ K1.ⓑ{I1}V1 →
                            ∀I2,K2,V2. ⬇*[i] L2 ≘ K2.ⓑ{I2}V2 →
                            ∧∧ K1 ≛[V1] K2 & V1 ≛ V2 & I1 = I2.
/2 width=6 by rex_inv_lref_pair_bi/ qed-.
