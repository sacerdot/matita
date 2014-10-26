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

include "basic_2/notation/relations/rminus_3.ma".
include "basic_2/multiple/mr2.ma".

(* MULTIPLE RELOCATION WITH PAIRS *******************************************)

inductive minuss: nat → relation (list2 nat nat) ≝
| minuss_nil: ∀i. minuss i (◊) (◊)
| minuss_lt : ∀des1,des2,l,m,i. i < l → minuss i des1 des2 →
              minuss i ({l, m} @ des1) ({l - i, m} @ des2)
| minuss_ge : ∀des1,des2,l,m,i. l ≤ i → minuss (m + i) des1 des2 →
              minuss i ({l, m} @ des1) des2
.

interpretation "minus (multiple relocation with pairs)"
   'RMinus des1 i des2 = (minuss i des1 des2).

(* Basic inversion lemmas ***************************************************)

fact minuss_inv_nil1_aux: ∀des1,des2,i. des1 ▭ i ≡ des2 → des1 = ◊ → des2 = ◊.
#des1 #des2 #i * -des1 -des2 -i
[ //
| #des1 #des2 #l #m #i #_ #_ #H destruct
| #des1 #des2 #l #m #i #_ #_ #H destruct
]
qed-.

lemma minuss_inv_nil1: ∀des2,i. ◊ ▭ i ≡ des2 → des2 = ◊.
/2 width=4 by minuss_inv_nil1_aux/ qed-.

fact minuss_inv_cons1_aux: ∀des1,des2,i. des1 ▭ i ≡ des2 →
                           ∀l,m,des. des1 = {l, m} @ des →
                           l ≤ i ∧ des ▭ m + i ≡ des2 ∨
                           ∃∃des0. i < l & des ▭ i ≡ des0 &
                                   des2 = {l - i, m} @ des0.
#des1 #des2 #i * -des1 -des2 -i
[ #i #l #m #des #H destruct
| #des1 #des #l1 #m1 #i1 #Hil1 #Hcs #l2 #m2 #des2 #H destruct /3 width=3 by ex3_intro, or_intror/
| #des1 #des #l1 #m1 #i1 #Hli1 #Hcs #l2 #m2 #des2 #H destruct /3 width=1 by or_introl, conj/
]
qed-.

lemma minuss_inv_cons1: ∀des1,des2,l,m,i. {l, m} @ des1 ▭ i ≡ des2 →
                        l ≤ i ∧ des1 ▭ m + i ≡ des2 ∨
                        ∃∃des. i < l & des1 ▭ i ≡ des &
                               des2 = {l - i, m} @ des.
/2 width=3 by minuss_inv_cons1_aux/ qed-.

lemma minuss_inv_cons1_ge: ∀des1,des2,l,m,i. {l, m} @ des1 ▭ i ≡ des2 →
                           l ≤ i → des1 ▭ m + i ≡ des2.
#des1 #des2 #l #m #i #H
elim (minuss_inv_cons1 … H) -H * // #des #Hil #_ #_ #Hli
lapply (lt_to_le_to_lt … Hil Hli) -Hil -Hli #Hi
elim (lt_refl_false … Hi)
qed-.

lemma minuss_inv_cons1_lt: ∀des1,des2,l,m,i. {l, m} @ des1 ▭ i ≡ des2 →
                           i < l →
                           ∃∃des. des1 ▭ i ≡ des & des2 = {l - i, m} @ des.
#des1 #des2 #l #m #i #H elim (minuss_inv_cons1 … H) -H * /2 width=3 by ex2_intro/
#Hli #_ #Hil lapply (lt_to_le_to_lt … Hil Hli) -Hil -Hli
#Hi elim (lt_refl_false … Hi)
qed-.
