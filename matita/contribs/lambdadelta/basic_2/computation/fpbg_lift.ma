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

include "basic_2/computation/fpbu_lift.ma".
include "basic_2/computation/fpbg.ma".

(* GENERAL "BIG TREE" PARALLEL COMPUTATION FOR CLOSURES *********************)

(* Advanced properties ******************************************************)

lemma lstas_fpbg: ∀h,g,G,L,T1,T2,l2. ⦃G, L⦄ ⊢ T1 •*[h, l2] T2 → (T1 = T2 → ⊥) →
                  ∀l1. l2 ≤ l1 → ⦃G, L⦄ ⊢ T1 ▪[h, g] l1 → ⦃G, L, T1⦄ >≡[h, g] ⦃G, L, T2⦄.
/5 width=5 by fpbc_fpbg, fpbu_fpbc, lstas_fpbu/ qed.

lemma sta_fpbg: ∀h,g,G,L,T1,T2,l. ⦃G, L⦄ ⊢ T1 ▪[h, g] l+1 →
                ⦃G, L⦄ ⊢ T1 •[h] T2 → ⦃G, L, T1⦄ >≡[h, g] ⦃G, L, T2⦄.
/4 width=2 by fpbc_fpbg, fpbu_fpbc, sta_fpbu/ qed.
