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

include "basic_2/computation/fpbc_lift.ma".
include "basic_2/computation/fpbg.ma".

(* GENERAL "BIG TREE" PARALLEL COMPUTATION FOR CLOSURES *********************)

(* Advanced properties ******************************************************)

lemma lsstas_fpbg: ∀h,g,G,L,T1,T2,l2. ⦃G, L⦄ ⊢ T1 •*[h, g, l2] T2 → (T1 = T2 → ⊥) →
                   ∀l1. l2 ≤ l1 → ⦃G, L⦄ ⊢ T1 ▪[h, g] l1 → ⦃G, L, T1⦄ >[h, g] ⦃G, L, T2⦄.
/4 width=5 by fpbc_fpbg, lsstas_fpbc/ qed.

lemma ssta_fpbg: ∀h,g,G,L,T1,T2,l. ⦃G, L⦄ ⊢ T1 ▪[h, g] l+1 →
                 ⦃G, L⦄ ⊢ T1 •[h, g] T2 → ⦃G, L, T1⦄ >[h, g] ⦃G, L, T2⦄.
/3 width=2 by fpbc_fpbg, ssta_fpbc/ qed.
