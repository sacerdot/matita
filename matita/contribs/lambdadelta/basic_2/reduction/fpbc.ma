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

lemma fpb_fpbc_or_fpn: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≽[h, g] ⦃G2, L2, T2⦄ →
                       ⦃G1, L1, T1⦄ ≻[h, g] ⦃G2, L2, T2⦄ ∨
                       ⦃G1, L1, T1⦄ ⊢ ➡[h,g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 * -G2 -L2 -T2
/3 width=1 by and3_intro, or_intror/
[ #G2 #L2 #T2 #H elim (fquq_inv_gen … H) -H [| * ]
  /3 width=1 by fpbc_fqu, and3_intro, or_introl, or_intror/
| #T2 #HT12 elim (term_eq_dec T1 T2) #H destruct
  /4 width=1 by and3_intro, or_introl, or_intror, fpbc_cpx/
]
qed-.

lemma fpb_fpbc: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≽[h, g] ⦃G2, L2, T2⦄ →
                (⦃G1, L1, T1⦄ ⋕ ⦃G2, L2, T2⦄ → ⊥) →
                ⦃G1, L1, T1⦄ ≻[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H #H0 elim (fpb_fpbc_or_fpn … H) -H //
#H elim H0 -H0 /2 width=3 by fpn_fwd_bteq/
qed.

(* Basic forward lemmas *****************************************************)

lemma fpbc_fwd_fpb: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≻[h, g] ⦃G2, L2, T2⦄ →
                    ⦃G1, L1, T1⦄ ≽[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 * -G2 -L2 -T2
/3 width=1 by fpb_fquq, fpb_cpx, fqu_fquq/
qed-.

lemma fpbc_fwd_bteq: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≻[h, g] ⦃G2, L2, T2⦄ →
                     ⦃G1, L1, T1⦄ ⋕ ⦃G2, L2, T2⦄ → ⊥.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 * -G2 -L2 -T2 /2 width=8 by fqu_fwd_bteq/
#T2 #_ #HT12 * /2 width=1 by/
qed-.
