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
include "basic_2/reduction/ypr.ma".

(* "BIG TREE" PROPER PARALLEL REDUCTION FOR CLOSURES ************************)

inductive ysc (h) (g) (G1) (L1) (T1): relation3 genv lenv term ≝
| ysc_fsup  : ∀G2,L2,T2. ⦃G1, L1, T1⦄ ⊃ ⦃G2, L2, T2⦄ → ysc h g G1 L1 T1 G2 L2 T2
| ysc_cpr   : ∀T2. ⦃G1, L1⦄ ⊢ T1 ➡ T2 → (T1 = T2 → ⊥) → ysc h g G1 L1 T1 G1 L1 T2
| ysc_ssta  : ∀T2,l. ⦃G1, L1⦄ ⊢ T1 ▪[h, g] l+1 → ⦃G1, L1⦄ ⊢ T1 •[h, g] T2 → ysc h g G1 L1 T1 G1 L1 T2
.

interpretation
   "'big tree' proper parallel reduction (closure)"
   'BTPRedProper h g G1 L1 T1 G2 L2 T2 = (ysc h g G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

lemma ysc_ypr: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≻[h, g] ⦃G2, L2, T2⦄ →
               ⦃G1, L1, T1⦄ ≽[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 * -G2 -L2 -T2
/2 width=2 by ypr_fsup, ypr_cpr, ypr_ssta/
qed.

(* Inversion lemmas on "big tree" parallel reduction for closures ***********)

lemma ypr_inv_ysc: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≽[h, g] ⦃G2, L2, T2⦄ →
                   ⦃G1, L1, T1⦄ ≻[h, g] ⦃G2, L2, T2⦄ ∨
                   ∧∧ G1 = G2 & ⦃G1, L1⦄ ⊢ ➡ L2 & T1 = T2.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 * -G2 -L2 -T2
/3 width=2 by and3_intro, or_introl, or_intror, ysc_fsup, ysc_ssta/
#T2 #HT12 elim (term_eq_dec T1 T2) #H destruct
/4 width=1 by and3_intro, or_introl, or_intror, ysc_cpr/
qed-.
