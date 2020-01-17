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

include "basic_2A/notation/relations/rat_3.ma".
include "basic_2A/grammar/term_vector.ma".

(* MULTIPLE RELOCATION WITH PAIRS *******************************************)

inductive at: list2 nat nat → relation nat ≝
| at_nil: ∀i. at (◊) i i
| at_lt : ∀cs,l,m,i1,i2. i1 < l →
          at cs i1 i2 → at ({l, m} @ cs) i1 i2
| at_ge : ∀cs,l,m,i1,i2. l ≤ i1 →
          at cs (i1 + m) i2 → at ({l, m} @ cs) i1 i2
.

interpretation "application (multiple relocation with pairs)"
   'RAt i1 cs i2 = (at cs i1 i2).

(* Basic inversion lemmas ***************************************************)

fact at_inv_nil_aux: ∀cs,i1,i2. @⦃i1, cs⦄ ≡ i2 → cs = ◊ → i1 = i2.
#cs #i1 #i2 * -cs -i1 -i2
[ //
| #cs #l #m #i1 #i2 #_ #_ #H destruct
| #cs #l #m #i1 #i2 #_ #_ #H destruct
]
qed-.

lemma at_inv_nil: ∀i1,i2. @⦃i1, ◊⦄ ≡ i2 → i1 = i2.
/2 width=3 by at_inv_nil_aux/ qed-.

fact at_inv_cons_aux: ∀cs,i1,i2. @⦃i1, cs⦄ ≡ i2 →
                      ∀l,m,cs0. cs = {l, m} @ cs0 →
                      i1 < l ∧ @⦃i1, cs0⦄ ≡ i2 ∨
                      l ≤ i1 ∧ @⦃i1 + m, cs0⦄ ≡ i2.
#cs #i1 #i2 * -cs -i1 -i2
[ #i #l #m #cs #H destruct
| #cs1 #l1 #m1 #i1 #i2 #Hil1 #Hi12 #l2 #m2 #cs2 #H destruct /3 width=1 by or_introl, conj/
| #cs1 #l1 #m1 #i1 #i2 #Hli1 #Hi12 #l2 #m2 #cs2 #H destruct /3 width=1 by or_intror, conj/
]
qed-.

lemma at_inv_cons: ∀cs,l,m,i1,i2. @⦃i1, {l, m} @ cs⦄ ≡ i2 →
                   i1 < l ∧ @⦃i1, cs⦄ ≡ i2 ∨
                   l ≤ i1 ∧ @⦃i1 + m, cs⦄ ≡ i2.
/2 width=3 by at_inv_cons_aux/ qed-.

lemma at_inv_cons_lt: ∀cs,l,m,i1,i2. @⦃i1, {l, m} @ cs⦄ ≡ i2 →
                      i1 < l → @⦃i1, cs⦄ ≡ i2.
#cs #l #m #i1 #m2 #H
elim (at_inv_cons … H) -H * // #Hli1 #_ #Hi1l
lapply (le_to_lt_to_lt … Hli1 Hi1l) -Hli1 -Hi1l #Hl
elim (lt_refl_false … Hl)
qed-.

lemma at_inv_cons_ge: ∀cs,l,m,i1,i2. @⦃i1, {l, m} @ cs⦄ ≡ i2 →
                      l ≤ i1 → @⦃i1 + m, cs⦄ ≡ i2.
#cs #l #m #i1 #m2 #H
elim (at_inv_cons … H) -H * // #Hi1l #_ #Hli1
lapply (le_to_lt_to_lt … Hli1 Hi1l) -Hli1 -Hi1l #Hl
elim (lt_refl_false … Hl)
qed-.
