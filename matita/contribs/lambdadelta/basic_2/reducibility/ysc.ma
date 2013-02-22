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

include "basic_2/static/ssta.ma".
include "basic_2/reducibility/cpr.ma".

(* "BIG TREE" SUCCESSOR ON CLOSURES *****************************************)

inductive ysc (h) (g) (L1) (T1): relation2 lenv term ≝
| ysc_fw  : ∀L2,T2. ♯{L2, T2} < ♯{L1, T1} → ysc h g L1 T1 L2 T2
| ysc_cpr : ∀T2. L1 ⊢ T1 ➡ T2 → (T1 = T2 → ⊥) → ysc h g L1 T1 L1 T2
| ysc_ssta: ∀T2,l. ⦃h, L1⦄ ⊢ T1 •[g, l + 1] T2 → ysc h g L1 T1 L1 T2
.

interpretation
   "'big tree' successor (closure)"
   'BTSuccessor h g L1 T1 L2 T2 = (ysc h g L1 T1 L2 T2).
