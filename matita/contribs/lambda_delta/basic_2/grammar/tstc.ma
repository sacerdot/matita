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

include "basic_2/grammar/term_simple.ma".

(* SAME TOP TERM CONSTRUCTOR ************************************************)

inductive tstc: relation term ≝
   | tstc_atom: ∀I. tstc (⓪{I}) (⓪{I})
   | tstc_pair: ∀I,V1,V2,T1,T2. tstc (②{I} V1. T1) (②{I} V2. T2)
.

interpretation "same top constructor (term)" 'Iso T1 T2 = (tstc T1 T2).

(* Basic inversion lemmas ***************************************************)

fact tstc_inv_atom1_aux: ∀T1,T2. T1 ≃ T2 → ∀I. T1 = ⓪{I} → T2 = ⓪{I}.
#T1 #T2 * -T1 -T2 //
#J #V1 #V2 #T1 #T2 #I #H destruct
qed.

(* Basic_1: was: iso_gen_sort iso_gen_lref *)
lemma tstc_inv_atom1: ∀I,T2. ⓪{I} ≃ T2 → T2 = ⓪{I}.
/2 width=3/ qed-.

fact tstc_inv_pair1_aux: ∀T1,T2. T1 ≃ T2 → ∀I,W1,U1. T1 = ②{I}W1.U1 →
                         ∃∃W2,U2. T2 = ②{I}W2. U2.
#T1 #T2 * -T1 -T2
[ #J #I #W1 #U1 #H destruct
| #J #V1 #V2 #T1 #T2 #I #W1 #U1 #H destruct /2 width=3/
]
qed.

(* Basic_1: was: iso_gen_head *)
lemma tstc_inv_pair1: ∀I,W1,U1,T2. ②{I}W1.U1 ≃ T2 →
                      ∃∃W2,U2. T2 = ②{I}W2. U2.
/2 width=5/ qed-.

fact tstc_inv_atom2_aux: ∀T1,T2. T1 ≃ T2 → ∀I. T2 = ⓪{I} → T1 = ⓪{I}.
#T1 #T2 * -T1 -T2 //
#J #V1 #V2 #T1 #T2 #I #H destruct
qed.

lemma tstc_inv_atom2: ∀I,T1. T1 ≃ ⓪{I} → T1 = ⓪{I}.
/2 width=3/ qed-.

fact tstc_inv_pair2_aux: ∀T1,T2. T1 ≃ T2 → ∀I,W2,U2. T2 = ②{I}W2.U2 →
                         ∃∃W1,U1. T1 = ②{I}W1. U1.
#T1 #T2 * -T1 -T2
[ #J #I #W2 #U2 #H destruct
| #J #V1 #V2 #T1 #T2 #I #W2 #U2 #H destruct /2 width=3/
]
qed.

lemma tstc_inv_pair2: ∀I,T1,W2,U2. T1 ≃ ②{I}W2.U2 →
                      ∃∃W1,U1. T1 = ②{I}W1. U1.
/2 width=5/ qed-.

(* Basic properties *********************************************************)

(* Basic_1: was: iso_refl *)
lemma tstc_refl: ∀T. T ≃ T.
#T elim T -T //
qed.

lemma tstc_sym: ∀T1,T2. T1 ≃ T2 → T2 ≃ T1.
#T1 #T2 #H elim H -T1 -T2 //
qed.

lemma tstc_dec: ∀T1,T2. Decidable (T1 ≃ T2).
* #I1 [2: #V1 #T1 ] * #I2 [2,4: #V2 #T2 ]
[ elim (item2_eq_dec I1 I2) #HI12
  [ destruct /2 width=1/
  | @or_intror #H
    elim (tstc_inv_pair1 … H) -H #V #T #H destruct /2 width=1/
  ]
| @or_intror #H
  lapply (tstc_inv_atom1 … H) -H #H destruct
| @or_intror #H
  lapply (tstc_inv_atom2 … H) -H #H destruct
| elim (item0_eq_dec I1 I2) #HI12
  [ destruct /2 width=1/
  | @or_intror #H
    lapply (tstc_inv_atom2 … H) -H #H destruct /2 width=1/
  ]
]
qed.

lemma simple_tstc_repl_dx: ∀T1,T2. T1 ≃ T2 → 𝐒[T1] → 𝐒[T2].
#T1 #T2 * -T1 -T2 //
#I #V1 #V2 #T1 #T2 #H
elim (simple_inv_pair … H) -H #J #H destruct //
qed. (**) (* remove from index *)

lemma simple_tstc_repl_sn: ∀T1,T2. T1 ≃ T2 → 𝐒[T2] → 𝐒[T1].
/3 width=3/ qed-.
