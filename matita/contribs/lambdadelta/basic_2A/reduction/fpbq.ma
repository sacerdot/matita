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

include "basic_2A/notation/relations/btpred_8.ma".
include "basic_2A/substitution/fquq.ma".
include "basic_2A/multiple/lleq.ma".
include "basic_2A/reduction/lpx.ma".

(* "QRST" PARALLEL REDUCTION FOR CLOSURES ***********************************)

inductive fpbq (h) (g) (G1) (L1) (T1): relation3 genv lenv term ≝
| fpbq_fquq: ∀G2,L2,T2. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄ → fpbq h g G1 L1 T1 G2 L2 T2
| fpbq_cpx : ∀T2. ⦃G1, L1⦄ ⊢ T1 ➡[h, g] T2 → fpbq h g G1 L1 T1 G1 L1 T2
| fpbq_lpx : ∀L2. ⦃G1, L1⦄ ⊢ ➡[h, g] L2 → fpbq h g G1 L1 T1 G1 L2 T1
| fpbq_lleq: ∀L2. L1 ≡[T1, 0] L2 → fpbq h g G1 L1 T1 G1 L2 T1
.

interpretation
   "'qrst' parallel reduction (closure)"
   'BTPRed h g G1 L1 T1 G2 L2 T2 = (fpbq h g G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

lemma fpbq_refl: ∀h,g. tri_reflexive … (fpbq h g).
/2 width=1 by fpbq_cpx/ qed.

lemma cpr_fpbq: ∀h,g,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡ T2 → ⦃G, L, T1⦄ ≽[h, g] ⦃G, L, T2⦄. 
/3 width=1 by fpbq_cpx, cpr_cpx/ qed.

lemma lpr_fpbq: ∀h,g,G,L1,L2,T. ⦃G, L1⦄ ⊢ ➡ L2 → ⦃G, L1, T⦄ ≽[h, g] ⦃G, L2, T⦄.
/3 width=1 by fpbq_lpx, lpr_lpx/ qed.
