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
| minuss_nil: ∀i. minuss i (⟠) (⟠)
| minuss_lt : ∀des1,des2,d,e,i. i < d → minuss i des1 des2 →
              minuss i ({d, e} @ des1) ({d - i, e} @ des2)
| minuss_ge : ∀des1,des2,d,e,i. d ≤ i → minuss (e + i) des1 des2 →
              minuss i ({d, e} @ des1) des2
.

interpretation "minus (multiple relocation with pairs)"
   'RMinus des1 i des2 = (minuss i des1 des2).

(* Basic inversion lemmas ***************************************************)

fact minuss_inv_nil1_aux: ∀des1,des2,i. des1 ▭ i ≡ des2 → des1 = ⟠ → des2 = ⟠.
#des1 #des2 #i * -des1 -des2 -i
[ //
| #des1 #des2 #d #e #i #_ #_ #H destruct
| #des1 #des2 #d #e #i #_ #_ #H destruct
]
qed-.

lemma minuss_inv_nil1: ∀des2,i. ⟠ ▭ i ≡ des2 → des2 = ⟠.
/2 width=4 by minuss_inv_nil1_aux/ qed-.

fact minuss_inv_cons1_aux: ∀des1,des2,i. des1 ▭ i ≡ des2 →
                           ∀d,e,des. des1 = {d, e} @ des →
                           d ≤ i ∧ des ▭ e + i ≡ des2 ∨
                           ∃∃des0. i < d & des ▭ i ≡ des0 &
                                   des2 = {d - i, e} @ des0.
#des1 #des2 #i * -des1 -des2 -i
[ #i #d #e #des #H destruct
| #des1 #des #d1 #e1 #i1 #Hid1 #Hdes #d2 #e2 #des2 #H destruct /3 width=3 by ex3_intro, or_intror/
| #des1 #des #d1 #e1 #i1 #Hdi1 #Hdes #d2 #e2 #des2 #H destruct /3 width=1 by or_introl, conj/
]
qed-.

lemma minuss_inv_cons1: ∀des1,des2,d,e,i. {d, e} @ des1 ▭ i ≡ des2 →
                        d ≤ i ∧ des1 ▭ e + i ≡ des2 ∨
                        ∃∃des. i < d & des1 ▭ i ≡ des &
                               des2 = {d - i, e} @ des.
/2 width=3 by minuss_inv_cons1_aux/ qed-.

lemma minuss_inv_cons1_ge: ∀des1,des2,d,e,i. {d, e} @ des1 ▭ i ≡ des2 →
                           d ≤ i → des1 ▭ e + i ≡ des2.
#des1 #des2 #d #e #i #H
elim (minuss_inv_cons1 … H) -H * // #des #Hid #_ #_ #Hdi
lapply (lt_to_le_to_lt … Hid Hdi) -Hid -Hdi #Hi
elim (lt_refl_false … Hi)
qed-.

lemma minuss_inv_cons1_lt: ∀des1,des2,d,e,i. {d, e} @ des1 ▭ i ≡ des2 →
                           i < d →
                           ∃∃des. des1 ▭ i ≡ des & des2 = {d - i, e} @ des.
#des1 #des2 #d #e #i #H elim (minuss_inv_cons1 … H) -H * /2 width=3 by ex2_intro/
#Hdi #_ #Hid lapply (lt_to_le_to_lt … Hid Hdi) -Hid -Hdi
#Hi elim (lt_refl_false … Hi)
qed-.
