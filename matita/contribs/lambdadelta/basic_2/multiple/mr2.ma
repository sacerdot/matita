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

include "basic_2/notation/relations/rat_3.ma".
include "basic_2/grammar/term_vector.ma".

(* MULTIPLE RELOCATION WITH PAIRS *******************************************)

inductive at: list2 nat nat → relation nat ≝
| at_nil: ∀i. at (◊) i i
| at_lt : ∀des,l,m,i1,i2. i1 < l →
          at des i1 i2 → at ({l, m} @ des) i1 i2
| at_ge : ∀des,l,m,i1,i2. l ≤ i1 →
          at des (i1 + m) i2 → at ({l, m} @ des) i1 i2
.

interpretation "application (multiple relocation with pairs)"
   'RAt i1 des i2 = (at des i1 i2).

(* Basic inversion lemmas ***************************************************)

fact at_inv_nil_aux: ∀des,i1,i2. @⦃i1, des⦄ ≡ i2 → des = ◊ → i1 = i2.
#des #i1 #i2 * -des -i1 -i2
[ //
| #des #l #m #i1 #i2 #_ #_ #H destruct
| #des #l #m #i1 #i2 #_ #_ #H destruct
]
qed-.

lemma at_inv_nil: ∀i1,i2. @⦃i1, ◊⦄ ≡ i2 → i1 = i2.
/2 width=3 by at_inv_nil_aux/ qed-.

fact at_inv_cons_aux: ∀des,i1,i2. @⦃i1, des⦄ ≡ i2 →
                      ∀l,m,des0. des = {l, m} @ des0 →
                      i1 < l ∧ @⦃i1, des0⦄ ≡ i2 ∨
                      l ≤ i1 ∧ @⦃i1 + m, des0⦄ ≡ i2.
#des #i1 #i2 * -des -i1 -i2
[ #i #l #m #des #H destruct
| #des1 #l1 #m1 #i1 #i2 #Hil1 #Hi12 #l2 #m2 #des2 #H destruct /3 width=1 by or_introl, conj/
| #des1 #l1 #m1 #i1 #i2 #Hli1 #Hi12 #l2 #m2 #des2 #H destruct /3 width=1 by or_intror, conj/
]
qed-.

lemma at_inv_cons: ∀des,l,m,i1,i2. @⦃i1, {l, m} @ des⦄ ≡ i2 →
                   i1 < l ∧ @⦃i1, des⦄ ≡ i2 ∨
                   l ≤ i1 ∧ @⦃i1 + m, des⦄ ≡ i2.
/2 width=3 by at_inv_cons_aux/ qed-.

lemma at_inv_cons_lt: ∀des,l,m,i1,i2. @⦃i1, {l, m} @ des⦄ ≡ i2 →
                      i1 < l → @⦃i1, des⦄ ≡ i2.
#des #l #m #i1 #m2 #H
elim (at_inv_cons … H) -H * // #Hli1 #_ #Hi1l
lapply (le_to_lt_to_lt … Hli1 Hi1l) -Hli1 -Hi1l #Hl
elim (lt_refl_false … Hl)
qed-.

lemma at_inv_cons_ge: ∀des,l,m,i1,i2. @⦃i1, {l, m} @ des⦄ ≡ i2 →
                      l ≤ i1 → @⦃i1 + m, des⦄ ≡ i2.
#des #l #m #i1 #m2 #H
elim (at_inv_cons … H) -H * // #Hi1l #_ #Hli1
lapply (le_to_lt_to_lt … Hli1 Hi1l) -Hli1 -Hi1l #Hl
elim (lt_refl_false … Hl)
qed-.
