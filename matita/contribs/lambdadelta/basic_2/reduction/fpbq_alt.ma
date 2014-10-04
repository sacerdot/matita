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

include "basic_2/notation/relations/btpredalt_8.ma".
include "basic_2/reduction/fpb_fleq.ma".
include "basic_2/reduction/fpbq.ma".

(* "QRST" PARALLEL REDUCTION FOR CLOSURES ***********************************)

(* alternative definition of fpbq *)
definition fpbqa: ∀h. sd h → tri_relation genv lenv term ≝
                  λh,g,G1,L1,T1,G2,L2,T2.
                  ⦃G1, L1, T1⦄ ≡[0] ⦃G2, L2, T2⦄ ∨ ⦃G1, L1, T1⦄ ≻[h, g] ⦃G2, L2, T2⦄.

interpretation
   "'qrst' parallel reduction (closure) alternative"
   'BTPRedAlt h g G1 L1 T1 G2 L2 T2 = (fpbqa h g G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

lemma fleq_fpbq: ∀h,g,G1,G2,L1,L2,T1,T2.
                 ⦃G1, L1, T1⦄ ≡[0] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ≽[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 * /2 width=1 by fpbq_lleq/
qed.

lemma fpb_fpbq: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≻[h, g] ⦃G2, L2, T2⦄ →
                ⦃G1, L1, T1⦄ ≽[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 * -G2 -L2 -T2
/3 width=1 by fpbq_fquq, fpbq_cpx, fpbq_lpx, fqu_fquq/
qed.

(* Main properties **********************************************************)

theorem fpbq_fpbqa: ∀h,g,G1,G2,L1,L2,T1,T2.
                    ⦃G1, L1, T1⦄ ≽[h, g] ⦃G2, L2, T2⦄ →
                    ⦃G1, L1, T1⦄ ≽≽[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 * -G2 -L2 -T2
[ #G2 #L2 #T2 #H elim (fquq_inv_gen … H) -H
  [ /3 width=1 by fpb_fqu, or_intror/
  | * #H1 #H2 #H3 destruct /2 width=1 by or_introl/
  ]
| #T2 #HT12 elim (eq_term_dec T1 T2)
  #HnT12 destruct /4 width=1 by fpb_cpx, or_intror, or_introl/
| #L2 #HL12 elim (lleq_dec … T1 L1 L2 0)
  /4 width=1 by fpb_lpx, fleq_intro, or_intror, or_introl/
| /3 width=1 by fleq_intro, or_introl/
]
qed.

theorem fpbqa_inv_fpbq: ∀h,g,G1,G2,L1,L2,T1,T2.
                        ⦃G1, L1, T1⦄ ≽≽[h, g] ⦃G2, L2, T2⦄ →
                        ⦃G1, L1, T1⦄ ≽[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 * /2 width=1 by fleq_fpbq, fpb_fpbq/
qed-.

(* Advanced eliminators *****************************************************)

lemma fpbq_ind_alt: ∀h,g,G1,G2,L1,L2,T1,T2. ∀R:Prop.
                    (⦃G1, L1, T1⦄ ≡[0] ⦃G2, L2, T2⦄ → R) →
                    (⦃G1, L1, T1⦄ ≻[h, g] ⦃G2, L2, T2⦄ → R) →
                    ⦃G1, L1, T1⦄ ≽[h, g] ⦃G2, L2, T2⦄ → R.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #R #HI1 #HI2 #H elim (fpbq_fpbqa … H) /2 width=1 by/
qed-.

(* aternative definition of fpb *********************************************)

lemma fpb_fpbq_alt: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≻[h, g] ⦃G2, L2, T2⦄ →
                    ⦃G1, L1, T1⦄ ≽[h, g] ⦃G2, L2, T2⦄ ∧ (⦃G1, L1, T1⦄ ≡[0] ⦃G2, L2, T2⦄ → ⊥).
/3 width=10 by fpb_fpbq, fpb_inv_fleq, conj/ qed.

lemma fpbq_inv_fpb_alt: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≽[h, g] ⦃G2, L2, T2⦄ →
                        (⦃G1, L1, T1⦄ ≡[0] ⦃G2, L2, T2⦄ → ⊥) → ⦃G1, L1, T1⦄ ≻[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H #H0 @(fpbq_ind_alt … H) -H //
#H elim H0 -H0 //
qed-.
