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
include "basic_2/reduction/fpbc.ma".
include "basic_2/computation/fpbs.ma".

(* GENEARAL "BIG TREE" PROPER PARALLEL COMPUTATION FOR CLOSURES *************)

inductive fpbg (h) (g) (G1) (L1) (T1): relation3 genv lenv term ≝
| fpbg_cpxs: ∀L2,T2. ⦃G1, L1⦄ ⊢ T1 ➡*[h, g] T2 → (T1 = T2 → ⊥) → ⦃G1, L1⦄ ⊢ ➡*[h, g] L2 →
             fpbg h g G1 L1 T1 G1 L2 T2
| fpbg_fqup: ∀G2,L,L2,T,T2. ⦃G1, L1⦄ ⊢ T1 ➡*[h, g] T → ⦃G1, L1, T⦄ ⊃+ ⦃G2, L, T2⦄ → ⦃G2, L⦄ ⊢ ➡*[h, g] L2 →
             fpbg h g G1 L1 T1 G2 L2 T2
.

interpretation "'big tree' proper parallel computation (closure)"
   'BTPRedStarProper h g G1 L1 T1 G2 L2 T2 = (fpbg h g G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

lemma fpbc_fpbg: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≻[h, g] ⦃G2, L2, T2⦄ →
                 ⦃G1, L1, T1⦄ >[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 * -G2 -L2 -T2
/3 width=5 by fpbg_cpxs, fpbg_fqup, fqu_fqup, cpx_cpxs/
qed.

axiom fpbg_strap1: ∀h,g,G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ >[h, g] ⦃G, L, T⦄ →
                   ⦃G, L, T⦄ ≽[h, g] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ >[h, g] ⦃G2, L2, T2⦄.

axiom fpbg_strap2: ∀h,g,G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ≽[h, g] ⦃G, L, T⦄ →
                   ⦃G, L, T⦄ >[h, g] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ >[h, g] ⦃G2, L2, T2⦄.

lemma fpbg_fpbs_trans: ∀h,g,G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ >[h, g] ⦃G, L, T⦄ →
                       ⦃G, L, T⦄ ≥[h, g] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ >[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G #G2 #L1 #L #L2 #T1 #T #T2 #H1 #H @(fpbs_ind … H) -G2 -L2 -T2
/2 width=5 by fpbg_strap1/
qed-.

lemma fpbs_fpbg_trans: ∀h,g,G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ≥[h, g] ⦃G, L, T⦄ →
                       ⦃G, L, T⦄ >[h, g] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ >[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G #G2 #L1 #L #L2 #T1 #T #T2 #H @(fpbs_ind_dx … H) -G1 -L1 -T1
/3 width=5 by fpbg_strap2/
qed-.
