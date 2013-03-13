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

include "basic_2/dynamic/ypr.ma".

(* "BIG TREE" PROPER PARALLEL REDUCTION FOR CLOSURES ************************)

inductive ysc (h) (g) (L1) (T1): relation2 lenv term ≝
| ysc_fw    : ∀L2,T2. ♯{L2, T2} < ♯{L1, T1} → ysc h g L1 T1 L2 T2
| ysc_cpr   : ∀T2. L1 ⊢ T1 ➡ T2 → (T1 = T2 → ⊥) → ysc h g L1 T1 L1 T2
| ysc_ssta  : ∀T2,l. ⦃h, L1⦄ ⊢ T1 •[g, l + 1] T2 → ysc h g L1 T1 L1 T2
| ysc_lsubsv: ∀L2. h ⊢ L2 ⊩:⊑[g] L1 → (L1 = L2 → ⊥) → ysc h g L1 T1 L2 T1
.

interpretation
   "'big tree' proper parallel reduction (closure)"
   'BTPRedProper h g L1 T1 L2 T2 = (ysc h g L1 T1 L2 T2).

(* Basic properties *********************************************************)

lemma ysc_ypr: ∀h,g,L1,L2,T1,T2. h ⊢ ⦃L1, T1⦄ ≻[g] ⦃L2, T2⦄ →
               h ⊢ ⦃L1, T1⦄ ≽[g] ⦃L2, T2⦄.
#h #g #L1 #L2 #T1 #T2 * -L2 -T2 /2 width=1/ /2 width=2/
qed.

(* Inversion lemmas on "big tree" parallel reduction for closures ***********)

lemma ypr_inv_ysc: ∀h,g,L1,L2,T1,T2. h ⊢ ⦃L1, T1⦄ ≽[g] ⦃L2, T2⦄ →
                   h ⊢ ⦃L1, T1⦄ ≻[g] ⦃L2, T2⦄ ∨ (L1 ➡ L2 ∧ T1 = T2).
#h #g #L1 #L2 #T1 #T2 * -L2 -T2 /3 width=1/ /3 width=2/
[ #T2 #HT12 elim (term_eq_dec T1 T2) #H destruct /3 width=1/ /4 width=1/
| #L2 #HL21 elim (lenv_eq_dec L1 L2) #H destruct /3 width=1/ /4 width=1/
]
qed-.
