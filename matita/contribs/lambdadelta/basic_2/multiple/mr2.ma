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
| at_nil: ∀i. at (⟠) i i
| at_lt : ∀des,d,e,i1,i2. i1 < d →
          at des i1 i2 → at ({d, e} @ des) i1 i2
| at_ge : ∀des,d,e,i1,i2. d ≤ i1 →
          at des (i1 + e) i2 → at ({d, e} @ des) i1 i2
.

interpretation "application (multiple relocation with pairs)"
   'RAt i1 des i2 = (at des i1 i2).

(* Basic inversion lemmas ***************************************************)

fact at_inv_nil_aux: ∀des,i1,i2. @⦃i1, des⦄ ≡ i2 → des = ⟠ → i1 = i2.
#des #i1 #i2 * -des -i1 -i2
[ //
| #des #d #e #i1 #i2 #_ #_ #H destruct
| #des #d #e #i1 #i2 #_ #_ #H destruct
]
qed-.

lemma at_inv_nil: ∀i1,i2. @⦃i1, ⟠⦄ ≡ i2 → i1 = i2.
/2 width=3 by at_inv_nil_aux/ qed-.

fact at_inv_cons_aux: ∀des,i1,i2. @⦃i1, des⦄ ≡ i2 →
                      ∀d,e,des0. des = {d, e} @ des0 →
                      i1 < d ∧ @⦃i1, des0⦄ ≡ i2 ∨
                      d ≤ i1 ∧ @⦃i1 + e, des0⦄ ≡ i2.
#des #i1 #i2 * -des -i1 -i2
[ #i #d #e #des #H destruct
| #des1 #d1 #e1 #i1 #i2 #Hid1 #Hi12 #d2 #e2 #des2 #H destruct /3 width=1 by or_introl, conj/
| #des1 #d1 #e1 #i1 #i2 #Hdi1 #Hi12 #d2 #e2 #des2 #H destruct /3 width=1 by or_intror, conj/
]
qed-.

lemma at_inv_cons: ∀des,d,e,i1,i2. @⦃i1, {d, e} @ des⦄ ≡ i2 →
                   i1 < d ∧ @⦃i1, des⦄ ≡ i2 ∨
                   d ≤ i1 ∧ @⦃i1 + e, des⦄ ≡ i2.
/2 width=3 by at_inv_cons_aux/ qed-.

lemma at_inv_cons_lt: ∀des,d,e,i1,i2. @⦃i1, {d, e} @ des⦄ ≡ i2 →
                      i1 < d → @⦃i1, des⦄ ≡ i2.
#des #d #e #i1 #e2 #H
elim (at_inv_cons … H) -H * // #Hdi1 #_ #Hi1d
lapply (le_to_lt_to_lt … Hdi1 Hi1d) -Hdi1 -Hi1d #Hd
elim (lt_refl_false … Hd)
qed-.

lemma at_inv_cons_ge: ∀des,d,e,i1,i2. @⦃i1, {d, e} @ des⦄ ≡ i2 →
                      d ≤ i1 → @⦃i1 + e, des⦄ ≡ i2.
#des #d #e #i1 #e2 #H
elim (at_inv_cons … H) -H * // #Hi1d #_ #Hdi1
lapply (le_to_lt_to_lt … Hdi1 Hi1d) -Hdi1 -Hi1d #Hd
elim (lt_refl_false … Hd)
qed-.
