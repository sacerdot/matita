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

include "ground_2/notation/relations/rminus_3.ma".
include "ground_2/relocation/mr2.ma".

(* MULTIPLE RELOCATION WITH PAIRS *******************************************)

inductive minuss: nat → relation mr2 ≝
| minuss_nil: ∀i. minuss i (◊) (◊)
| minuss_lt : ∀cs1,cs2,l,m,i. i < l → minuss i cs1 cs2 →
              minuss i ({l, m} @ cs1) ({l - i, m} @ cs2)
| minuss_ge : ∀cs1,cs2,l,m,i. l ≤ i → minuss (m + i) cs1 cs2 →
              minuss i ({l, m} @ cs1) cs2
.

interpretation "minus (multiple relocation with pairs)"
   'RMinus cs1 i cs2 = (minuss i cs1 cs2).

(* Basic inversion lemmas ***************************************************)

fact minuss_inv_nil1_aux: ∀cs1,cs2,i. cs1 ▭ i ≘ cs2 → cs1 = ◊ → cs2 = ◊.
#cs1 #cs2 #i * -cs1 -cs2 -i
[ //
| #cs1 #cs2 #l #m #i #_ #_ #H destruct
| #cs1 #cs2 #l #m #i #_ #_ #H destruct
]
qed-.

lemma minuss_inv_nil1: ∀cs2,i. ◊ ▭ i ≘ cs2 → cs2 = ◊.
/2 width=4 by minuss_inv_nil1_aux/ qed-.

fact minuss_inv_cons1_aux: ∀cs1,cs2,i. cs1 ▭ i ≘ cs2 →
                           ∀l,m,cs. cs1 = {l, m} @ cs →
                           l ≤ i ∧ cs ▭ m + i ≘ cs2 ∨
                           ∃∃cs0. i < l & cs ▭ i ≘ cs0 &
                                   cs2 = {l - i, m} @ cs0.
#cs1 #cs2 #i * -cs1 -cs2 -i
[ #i #l #m #cs #H destruct
| #cs1 #cs #l1 #m1 #i1 #Hil1 #Hcs #l2 #m2 #cs2 #H destruct /3 width=3 by ex3_intro, or_intror/
| #cs1 #cs #l1 #m1 #i1 #Hli1 #Hcs #l2 #m2 #cs2 #H destruct /3 width=1 by or_introl, conj/
]
qed-.

lemma minuss_inv_cons1: ∀cs1,cs2,l,m,i. {l, m} @ cs1 ▭ i ≘ cs2 →
                        l ≤ i ∧ cs1 ▭ m + i ≘ cs2 ∨
                        ∃∃cs. i < l & cs1 ▭ i ≘ cs &
                               cs2 = {l - i, m} @ cs.
/2 width=3 by minuss_inv_cons1_aux/ qed-.

lemma minuss_inv_cons1_ge: ∀cs1,cs2,l,m,i. {l, m} @ cs1 ▭ i ≘ cs2 →
                           l ≤ i → cs1 ▭ m + i ≘ cs2.
#cs1 #cs2 #l #m #i #H
elim (minuss_inv_cons1 … H) -H * // #cs #Hil #_ #_ #Hli
elim (lt_le_false … Hil Hli)
qed-.

lemma minuss_inv_cons1_lt: ∀cs1,cs2,l,m,i. {l, m} @ cs1 ▭ i ≘ cs2 →
                           i < l →
                           ∃∃cs. cs1 ▭ i ≘ cs & cs2 = {l - i, m} @ cs.
#cs1 #cs2 #l #m #i #H elim (minuss_inv_cons1 … H) -H * /2 width=3 by ex2_intro/
#Hli #_ #Hil elim (lt_le_false … Hil Hli)
qed-.
