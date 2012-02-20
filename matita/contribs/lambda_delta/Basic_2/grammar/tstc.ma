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

include "Basic_2/grammar/term.ma".

(* SAME TOP TERM CONSTRUCTOR ************************************************)

inductive tstc: relation term ≝
   | tstc_atom: ∀I. tstc (⓪{I}) (⓪{I})
   | tstc_pair: ∀I,V1,V2,T1,T2. tstc (②{I} V1. T1) (②{I} V2. T2)
.

interpretation "same top constructor (term)" 'Iso T1 T2 = (tstc T1 T2).

(* Basic properties *********************************************************)

(* Basic_1: was: iso_refl *)
lemma tstc_refl: ∀T. T ≃ T.
#T elim T -T //
qed.

lemma tstc_sym: ∀T1,T2. T1 ≃ T2 → T2 ≃ T1.
#T1 #T2 #H elim H -T1 -T2 //
qed.

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

(* Basic_1: removed theorems 2:
            iso_flats_lref_bind_false iso_flats_flat_bind_false
*)
