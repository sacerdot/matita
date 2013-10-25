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

include "basic_2/computation/cpxs_lift.ma".
include "basic_2/computation/fpbs.ma".

(* "BIG TREE" PARALLEL COMPUTATION FOR CLOSURES *****************************)

(* Advanced properties ******************************************************)

lemma lsstas_fpbs: ∀h,g,G,L,T1,T2,l2. ⦃G, L⦄ ⊢ T1 •*[h, g, l2] T2 →
                   ∀l1. l2 ≤ l1 → ⦃G, L⦄ ⊢ T1 ▪[h, g] l1 → ⦃G, L, T1⦄ ≥[h, g] ⦃G, L, T2⦄.
/3 width=5 by cpxs_fpbs, lsstas_cpxs/ qed.

lemma ssta_fpbs: ∀h,g,G,L,T,U,l.
                 ⦃G, L⦄ ⊢ T ▪[h, g] l+1 → ⦃G, L⦄ ⊢ T •[h, g] U →
                 ⦃G, L, T⦄ ≥[h, g] ⦃G, L, U⦄.
/3 width=5 by lsstas_fpbs, ssta_lsstas/ qed.
