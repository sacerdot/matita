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

include "basic_2/notation/relations/topiso_2.ma".
include "basic_2/grammar/term_simple.ma".

(* SAME TOP TERM STRUCTURE **************************************************)

inductive tsts: relation term ≝
   | tsts_atom: ∀I. tsts (⓪{I}) (⓪{I})
   | tsts_pair: ∀I,V1,V2,T1,T2. tsts (②{I}V1.T1) (②{I}V2.T2)
.

interpretation "same top structure (term)" 'TopIso T1 T2 = (tsts T1 T2).

(* Basic inversion lemmas ***************************************************)

fact tsts_inv_atom1_aux: ∀T1,T2. T1 ≂ T2 → ∀I. T1 = ⓪{I} → T2 = ⓪{I}.
#T1 #T2 * -T1 -T2 //
#J #V1 #V2 #T1 #T2 #I #H destruct
qed-.

(* Basic_1: was: iso_gen_sort iso_gen_lref *)
lemma tsts_inv_atom1: ∀I,T2. ⓪{I} ≂ T2 → T2 = ⓪{I}.
/2 width=3 by tsts_inv_atom1_aux/ qed-.

fact tsts_inv_pair1_aux: ∀T1,T2. T1 ≂ T2 → ∀I,W1,U1. T1 = ②{I}W1.U1 →
                         ∃∃W2,U2. T2 = ②{I}W2. U2.
#T1 #T2 * -T1 -T2
[ #J #I #W1 #U1 #H destruct
| #J #V1 #V2 #T1 #T2 #I #W1 #U1 #H destruct /2 width=3 by ex1_2_intro/
]
qed-.

(* Basic_1: was: iso_gen_head *)
lemma tsts_inv_pair1: ∀I,W1,U1,T2. ②{I}W1.U1 ≂ T2 →
                      ∃∃W2,U2. T2 = ②{I}W2. U2.
/2 width=5 by tsts_inv_pair1_aux/ qed-.

fact tsts_inv_atom2_aux: ∀T1,T2. T1 ≂ T2 → ∀I. T2 = ⓪{I} → T1 = ⓪{I}.
#T1 #T2 * -T1 -T2 //
#J #V1 #V2 #T1 #T2 #I #H destruct
qed-.

lemma tsts_inv_atom2: ∀I,T1. T1 ≂ ⓪{I} → T1 = ⓪{I}.
/2 width=3 by tsts_inv_atom2_aux/ qed-.

fact tsts_inv_pair2_aux: ∀T1,T2. T1 ≂ T2 → ∀I,W2,U2. T2 = ②{I}W2.U2 →
                         ∃∃W1,U1. T1 = ②{I}W1.U1.
#T1 #T2 * -T1 -T2
[ #J #I #W2 #U2 #H destruct
| #J #V1 #V2 #T1 #T2 #I #W2 #U2 #H destruct /2 width=3 by ex1_2_intro/
]
qed-.

lemma tsts_inv_pair2: ∀I,T1,W2,U2. T1 ≂ ②{I}W2.U2 →
                      ∃∃W1,U1. T1 = ②{I}W1.U1.
/2 width=5 by tsts_inv_pair2_aux/ qed-.

(* Basic properties *********************************************************)

(* Basic_1: was: iso_refl *)
lemma tsts_refl: reflexive … tsts.
#T elim T -T //
qed.

lemma tsts_sym: symmetric … tsts.
#T1 #T2 #H elim H -T1 -T2 //
qed-.

lemma tsts_dec: ∀T1,T2. Decidable (T1 ≂ T2).
* #I1 [2: #V1 #T1 ] * #I2 [2,4: #V2 #T2 ]
[ elim (eq_item2_dec I1 I2) #HI12
  [ destruct /2 width=1 by tsts_pair, or_introl/
  | @or_intror #H
    elim (tsts_inv_pair1 … H) -H #V #T #H destruct /2 width=1 by/
  ]
| @or_intror #H
  lapply (tsts_inv_atom1 … H) -H #H destruct
| @or_intror #H
  lapply (tsts_inv_atom2 … H) -H #H destruct
| elim (eq_item0_dec I1 I2) #HI12
  [ destruct /2 width=1 by or_introl/
  | @or_intror #H
    lapply (tsts_inv_atom2 … H) -H #H destruct /2 width=1 by/
  ]
]
qed.

lemma simple_tsts_repl_dx: ∀T1,T2. T1 ≂ T2 → 𝐒⦃T1⦄ → 𝐒⦃T2⦄.
#T1 #T2 * -T1 -T2 //
#I #V1 #V2 #T1 #T2 #H
elim (simple_inv_pair … H) -H #J #H destruct //
qed-.

lemma simple_tsts_repl_sn: ∀T1,T2. T1 ≂ T2 → 𝐒⦃T2⦄ → 𝐒⦃T1⦄.
/3 width=3 by simple_tsts_repl_dx, tsts_sym/ qed-.
