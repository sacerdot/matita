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
include "basic_2/static/ssta.ma".
include "basic_2/reduction/lpr.ma".

(* "BIG TREE" PARALLEL REDUCTION FOR CLOSURES *******************************)

inductive fpb (h) (g) (G1) (L1) (T1): relation3 genv lenv term ≝
| fpb_fsup  : ∀G2,L2,T2. ⦃G1, L1, T1⦄ ⊃ ⦃G2, L2, T2⦄ → fpb h g G1 L1 T1 G2 L2 T2
| fpb_lpr   : ∀L2. ⦃G1, L1⦄ ⊢ ➡ L2 → fpb h g G1 L1 T1 G1 L2 T1
| fpb_cpr   : ∀T2. ⦃G1, L1⦄ ⊢ T1 ➡ T2 → fpb h g G1 L1 T1 G1 L1 T2
| fpb_ssta  : ∀T2,l. ⦃G1, L1⦄ ⊢ T1 ▪[h, g] l+1 → ⦃G1, L1⦄ ⊢ T1 •[h, g] T2 → fpb h g G1 L1 T1 G1 L1 T2
.

interpretation
   "'big tree' parallel reduction (closure)"
   'BTPRed h g G1 L1 T1 G2 L2 T2 = (fpb h g G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

lemma fpb_refl: ∀h,g. tri_reflexive … (fpb h g).
/2 width=1 by fpb_cpr/ qed.
