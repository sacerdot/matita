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

include "basic_2/notation/relations/btpred_8.ma".
include "basic_2/relocation/fsup.ma".
include "basic_2/reduction/lpr.ma".
include "basic_2/dynamic/lsubsv.ma".

(* "BIG TREE" PARALLEL REDUCTION FOR CLOSURES *******************************)

inductive ypr (h) (g) (G1) (L1) (T1): relation3 genv lenv term ≝
| ypr_fsup  : ∀G2,L2,T2. ⦃G1, L1, T1⦄ ⊃ ⦃G2, L2, T2⦄ → ypr h g G1 L1 T1 G2 L2 T2
| ypr_lpr   : ∀L2. ⦃G1, L1⦄ ⊢ ➡ L2 → ypr h g G1 L1 T1 G1 L2 T1
| ypr_cpr   : ∀T2. ⦃G1, L1⦄ ⊢ T1 ➡ T2 → ypr h g G1 L1 T1 G1 L1 T2
| ypr_ssta  : ∀T2,l. ⦃G1, L1⦄ ⊢ T1 ▪[h, g] l+1 → ⦃G1, L1⦄ ⊢ T1 •[h, g] T2 → ypr h g G1 L1 T1 G1 L1 T2
| ypr_lsubsv: ∀L2. G1 ⊢ L2 ¡⊑[h, g] L1 → ypr h g G1 L1 T1 G1 L2 T1
.

interpretation
   "'big tree' parallel reduction (closure)"
   'BTPRed h g G1 L1 T1 G2 L2 T2 = (ypr h g G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

lemma ypr_refl: ∀h,g. tri_reflexive … (ypr h g).
/2 width=1/ qed.
