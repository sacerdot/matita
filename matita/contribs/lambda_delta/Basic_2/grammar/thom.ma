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

include "Basic_2/grammar/term_simple.ma".

(* HOMOMORPHIC TERMS ********************************************************)

inductive thom: relation term ≝
   | thom_atom: ∀I. thom (⓪{I}) (⓪{I})
   | thom_abst: ∀V1,V2,T1,T2. thom (ⓛV1. T1) (ⓛV2. T2)
   | thom_appl: ∀V1,V2,T1,T2. thom T1 T2 → 𝕊[T1] → 𝕊[T2] →
                thom (ⓐV1. T1) (ⓐV2. T2)
.

interpretation "homomorphic (term)" 'napart T1 T2 = (thom T1 T2).

(* Basic properties *********************************************************)

lemma thom_sym: ∀T1,T2. T1 ≈ T2 → T2 ≈ T1.
#T1 #T2 #H elim H -T1 -T2 /2 width=1/
qed.

lemma thom_refl2: ∀T1,T2. T1 ≈ T2 → T2 ≈ T2.
#T1 #T2 #H elim H -T1 -T2 // /2 width=1/
qed.

lemma thom_refl1: ∀T1,T2. T1 ≈ T2 → T1 ≈ T1.
/3 width=2/ qed.

lemma simple_thom_repl_dx: ∀T1,T2. T1 ≈ T2 → 𝕊[T1] → 𝕊[T2].
#T1 #T2 #H elim H -T1 -T2 //
#V1 #V2 #T1 #T2 #H
elim (simple_inv_bind … H)
qed. (**) (* remove from index *)

lemma simple_thom_repl_sn: ∀T1,T2. T1 ≈ T2 → 𝕊[T2] → 𝕊[T1].
/3 width=3/ qed-.

(* Basic inversion lemmas ***************************************************)

fact thom_inv_bind1_aux: ∀T1,T2. T1 ≈ T2 → ∀I,W1,U1. T1 = ⓑ{I}W1.U1 →
                         ∃∃W2,U2. I = Abst & T2 = ⓛW2. U2.
#T1 #T2 * -T1 -T2
[ #J #I #W1 #U1 #H destruct
| #V1 #V2 #T1 #T2 #I #W1 #U1 #H destruct /2 width=3/
| #V1 #V2 #T1 #T2 #H_ #_ #_ #I #W1 #U1 #H destruct
]
qed.

lemma thom_inv_bind1: ∀I,W1,U1,T2. ⓑ{I}W1.U1 ≈ T2 →
                      ∃∃W2,U2. I = Abst & T2 = ⓛW2. U2.
/2 width=5/ qed-.

fact thom_inv_flat1_aux: ∀T1,T2. T1 ≈ T2 → ∀I,W1,U1. T1 = ⓕ{I}W1.U1 →
                         ∃∃W2,U2. U1 ≈ U2 & 𝕊[U1] & 𝕊[U2] &
                                  I = Appl & T2 = ⓐW2. U2.
#T1 #T2 * -T1 -T2
[ #J #I #W1 #U1 #H destruct
| #V1 #V2 #T1 #T2 #I #W1 #U1 #H destruct
| #V1 #V2 #T1 #T2 #HT12 #HT1 #HT2 #I #W1 #U1 #H destruct /2 width=5/
]
qed.

lemma thom_inv_flat1: ∀I,W1,U1,T2. ⓕ{I}W1.U1 ≈ T2 →
                      ∃∃W2,U2. U1 ≈ U2 & 𝕊[U1] & 𝕊[U2] &
                               I = Appl & T2 = ⓐW2. U2.
/2 width=4/ qed-.

(* Basic_1: removed theorems 7:
            iso_gen_sort iso_gen_lref iso_gen_head iso_refl iso_trans
            iso_flats_lref_bind_false iso_flats_flat_bind_false
*)
