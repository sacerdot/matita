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

include "basic_2/computation/ltprs.ma".
include "basic_2/dynamic/lsubsv.ma".

(* "BIG TREE" PROPER PARALLEL COMPUTATION FOR CLOSURES **********************)

axiom yprs: ∀h. sd h → bi_relation lenv term.

interpretation "'big tree' parallel computation (closure)"
   'BTPRedStar h g L1 T1 L2 T2 = (yprs h g L1 T1 L2 T2).

axiom cprs_yprs: ∀h,g,L,T1,T2. L ⊢ T1 ➡* T2 → h ⊢ ⦃L, T1⦄ ≥[g] ⦃L, T2⦄.

axiom sstas_yprs: ∀h,g,L,T1,T2. ⦃h, L⦄ ⊢ T1 •*[g] T2 →
                  h ⊢ ⦃L, T1⦄ ≥[g] ⦃L, T2⦄.

axiom lsubsv_yprs: ∀h,g,L1,L2,T. h ⊢ L2 ¡⊑[g] L1 → h ⊢ ⦃L1, T⦄ ≥[g] ⦃L2, T⦄.

axiom ltpr_cprs_yprs: ∀h,g,L1,L2,T1,T2. L1 ➡ L2 → L2 ⊢ T1 ➡* T2 →
                      h ⊢ ⦃L1, T1⦄ ≥[g] ⦃L2, T2⦄.

axiom ygt: ∀h. sd h → bi_relation lenv term.

interpretation "'big tree' proper parallel computation (closure)"
   'BTPRedStarProper h g L1 T1 L2 T2 = (ygt h g L1 T1 L2 T2).

axiom fw_ygt: ∀h,g,L1,L2,T1,T2. ♯{L2, T2} < ♯{L1, T1} → h ⊢ ⦃L1, T1⦄ >[g] ⦃L2, T2⦄.

axiom ygt_yprs_trans: ∀h,g,L1,L,L2,T1,T,T2. h ⊢ ⦃L1, T1⦄ >[g] ⦃L, T⦄ →
                      h ⊢ ⦃L, T⦄ ≥[g] ⦃L2, T2⦄ → h ⊢ ⦃L1, T1⦄ >[g] ⦃L2, T2⦄.
