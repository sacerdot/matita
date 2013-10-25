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

(* "BIG TREE" PROPER PARALLEL REDUCTION FOR CLOSURES ************************)

inductive fpbc (h) (g) (G1) (L1) (T1): relation3 genv lenv term ≝
| fpbc_fqu: ∀G2,L2,T2. ⦃G1, L1, T1⦄ ⊃ ⦃G2, L2, T2⦄ → fpbc h g G1 L1 T1 G2 L2 T2
| fpbc_cpx: ∀T2. ⦃G1, L1⦄ ⊢ T1 ➡[h, g] T2 → (T1 = T2 → ⊥) → fpbc h g G1 L1 T1 G1 L1 T2
.

interpretation
   "'big tree' proper parallel reduction (closure)"
   'BTPRedProper h g G1 L1 T1 G2 L2 T2 = (fpbc h g G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

lemma cpr_fpbc: ∀h,g,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡ T2 → (T1 = T2 → ⊥) →
                ⦃G, L, T1⦄ ≻[h, g] ⦃G, L, T2⦄.
/3 width=1 by fpbc_cpx, cpr_cpx/ qed.

(* Basic forward lemmas *****************************************************)

lemma fpbc_fwd_fpb: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≻[h, g] ⦃G2, L2, T2⦄ →
                    ⦃G1, L1, T1⦄ ≽[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 * -G2 -L2 -T2
/3 width=1 by fpb_fquq, fpb_cpx, fqu_fquq/
qed-.
