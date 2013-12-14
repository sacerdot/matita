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

include "basic_2/notation/relations/btpredstarproper_8.ma".
include "basic_2/computation/fpbc.ma".

(* GENEARAL "BIG TREE" PROPER PARALLEL COMPUTATION FOR CLOSURES *************)

(* Note: this is not transitive *)
inductive fpbg (h) (g) (G1) (L1) (T1): relation3 genv lenv term ≝
| fpbg_cpxs: ∀L2,T2. ⦃G1, L1⦄ ⊢ T1 ➡*[h, g] T2 → (T1 = T2 → ⊥) → ⦃G1, L1⦄ ⊢ ➡*[h, g] L2 →
             fpbg h g G1 L1 T1 G1 L2 T2
| fpbg_fqup: ∀G2,L,L2,T,T2. ⦃G1, L1⦄ ⊢ T1 ➡*[h, g] T → ⦃G1, L1, T⦄ ⊃+ ⦃G2, L, T2⦄ → ⦃G2, L⦄ ⊢ ➡*[h, g] L2 →
             fpbg h g G1 L1 T1 G2 L2 T2
| fpbg_lpxs: ∀G2,L,L0,L2,T,T2. ⦃G1, L1⦄ ⊢ T1 ➡*[h, g] T → ⦃G1, L1, T⦄ ⊃* ⦃G2, L, T2⦄ → ⦃G2, L⦄ ⊢ ➡*[h, g] L0 →
             (L ⋕[0, T2] L0 → ⊥) → ⦃G2, L0⦄ ⊢ ➡*[h, g] L2 → L0 ⋕[0, T2] L2 →
             fpbg h g G1 L1 T1 G2 L2 T2
.

interpretation "'big tree' proper parallel computation (closure)"
   'BTPRedStarProper h g G1 L1 T1 G2 L2 T2 = (fpbg h g G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

lemma fpbc_fpbg: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≻[h, g] ⦃G2, L2, T2⦄ →
                 ⦃G1, L1, T1⦄ >[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 * -G2 -L2 -T2
/3 width=9 by fpbg_fqup, fpbg_cpxs, fpbg_lpxs/
qed.
