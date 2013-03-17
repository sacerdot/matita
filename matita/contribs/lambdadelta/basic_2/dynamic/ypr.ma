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

include "basic_2/reducibility/ltpr.ma".
include "basic_2/dynamic/lsubsv.ma".

(* "BIG TREE" PARALLEL REDUCTION FOR CLOSURES *******************************)

inductive ypr (h) (g) (L1) (T1): relation2 lenv term ≝
| ypr_fw    : ∀L2,T2. ♯{L2, T2} < ♯{L1, T1} → ypr h g L1 T1 L2 T2
| ypr_ltpr  : ∀L2. L1 ➡ L2 → ypr h g L1 T1 L2 T1
| ypr_cpr   : ∀T2. L1 ⊢ T1 ➡ T2 → ypr h g L1 T1 L1 T2
| ypr_ssta  : ∀T2,l. ⦃h, L1⦄ ⊢ T1 •[g] ⦃l+1, T2⦄ → ypr h g L1 T1 L1 T2
| ypr_lsubsv: ∀L2. h ⊢ L2 ¡⊑[g] L1 → ypr h g L1 T1 L2 T1
.

interpretation
   "'big tree' parallel reduction (closure)"
   'BTPRed h g L1 T1 L2 T2 = (ypr h g L1 T1 L2 T2).

(* Basic properties *********************************************************)

lemma ypr_refl: ∀h,g. bi_reflexive … (ypr h g).
/2 width=1/ qed.
