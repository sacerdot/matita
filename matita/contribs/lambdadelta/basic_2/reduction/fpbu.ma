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

include "basic_2/notation/relations/btpredproper_8.ma".
include "basic_2/reduction/fpb.ma".

(* "RST" PROPER PARALLEL COMPUTATION FOR CLOSURES ***************************)

inductive fpbu (h) (g) (G1) (L1) (T1): relation3 genv lenv term ≝
| fpbu_fqu: ∀G2,L2,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ → fpbu h g G1 L1 T1 G2 L2 T2
| fpbu_cpx: ∀T2. ⦃G1, L1⦄ ⊢ T1 ➡[h, g] T2 → (T1 = T2 → ⊥) → fpbu h g G1 L1 T1 G1 L1 T2
| fpbu_lpx: ∀L2. ⦃G1, L1⦄ ⊢ ➡[h, g] L2 → (L1 ≡[T1, 0] L2 → ⊥) → fpbu h g G1 L1 T1 G1 L2 T1
.

interpretation
   "'rst' proper parallel reduction (closure)"
   'BTPRedProper h g G1 L1 T1 G2 L2 T2 = (fpbu h g G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

lemma cpr_fpbu: ∀h,g,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡ T2 → (T1 = T2 → ⊥) →
                ⦃G, L, T1⦄ ≻[h, g] ⦃G, L, T2⦄.
/3 width=1 by fpbu_cpx, cpr_cpx/ qed.

lemma lpr_fpbu: ∀h,g,G,L1,L2,T. ⦃G, L1⦄ ⊢ ➡ L2 → (L1 ≡[T, 0] L2 → ⊥) →
                ⦃G, L1, T⦄ ≻[h, g] ⦃G, L2, T⦄.
/3 width=1 by fpbu_lpx, lpr_lpx/ qed.

(* Basic forward lemmas *****************************************************)

lemma fpbu_fwd_fpb: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≻[h, g] ⦃G2, L2, T2⦄ →
                    ⦃G1, L1, T1⦄ ≽[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 * -G2 -L2 -T2
/3 width=1 by fpb_fquq, fpb_cpx, fpb_lpx, fqu_fquq/
qed-.
