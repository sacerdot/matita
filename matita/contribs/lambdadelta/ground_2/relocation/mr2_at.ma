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

include "ground_2/notation/relations/rat_3.ma".
include "ground_2/relocation/mr2.ma".

(* MULTIPLE RELOCATION WITH PAIRS *******************************************)

inductive at: mr2 → relation nat ≝
| at_nil: ∀i. at (◊) i i
| at_lt : ∀cs,l,m,i1,i2. i1 < l →
          at cs i1 i2 → at ({l, m};cs) i1 i2
| at_ge : ∀cs,l,m,i1,i2. l ≤ i1 →
          at cs (i1 + m) i2 → at ({l, m};cs) i1 i2
.

interpretation "application (multiple relocation with pairs)"
   'RAt i1 cs i2 = (at cs i1 i2).

(* Basic inversion lemmas ***************************************************)

fact at_inv_nil_aux: ∀cs,i1,i2. @⦃i1, cs⦄ ≘ i2 → cs = ◊ → i1 = i2.
#cs #i1 #i2 * -cs -i1 -i2
[ //
| #cs #l #m #i1 #i2 #_ #_ #H destruct
| #cs #l #m #i1 #i2 #_ #_ #H destruct
]
qed-.

lemma at_inv_nil: ∀i1,i2. @⦃i1, ◊⦄ ≘ i2 → i1 = i2.
/2 width=3 by at_inv_nil_aux/ qed-.

fact at_inv_cons_aux: ∀cs,i1,i2. @⦃i1, cs⦄ ≘ i2 →
                      ∀l,m,cs0. cs = {l, m};cs0 →
                      i1 < l ∧ @⦃i1, cs0⦄ ≘ i2 ∨
                      l ≤ i1 ∧ @⦃i1 + m, cs0⦄ ≘ i2.
#cs #i1 #i2 * -cs -i1 -i2
[ #i #l #m #cs #H destruct
| #cs1 #l1 #m1 #i1 #i2 #Hil1 #Hi12 #l2 #m2 #cs2 #H destruct /3 width=1 by or_introl, conj/
| #cs1 #l1 #m1 #i1 #i2 #Hli1 #Hi12 #l2 #m2 #cs2 #H destruct /3 width=1 by or_intror, conj/
]
qed-.

lemma at_inv_cons: ∀cs,l,m,i1,i2. @⦃i1, {l, m};cs⦄ ≘ i2 →
                   i1 < l ∧ @⦃i1, cs⦄ ≘ i2 ∨
                   l ≤ i1 ∧ @⦃i1 + m, cs⦄ ≘ i2.
/2 width=3 by at_inv_cons_aux/ qed-.

lemma at_inv_cons_lt: ∀cs,l,m,i1,i2. @⦃i1, {l, m};cs⦄ ≘ i2 →
                      i1 < l → @⦃i1, cs⦄ ≘ i2.
#cs #l #m #i1 #m2 #H
elim (at_inv_cons … H) -H * // #Hli1 #_ #Hi1l
elim (lt_le_false … Hi1l Hli1)
qed-.

lemma at_inv_cons_ge: ∀cs,l,m,i1,i2. @⦃i1, {l, m};cs⦄ ≘ i2 →
                      l ≤ i1 → @⦃i1 + m, cs⦄ ≘ i2.
#cs #l #m #i1 #m2 #H
elim (at_inv_cons … H) -H * // #Hi1l #_ #Hli1
elim (lt_le_false … Hi1l Hli1)
qed-.

(* Main properties **********************************************************)

theorem at_mono: ∀cs,i,i1. @⦃i, cs⦄ ≘ i1 → ∀i2. @⦃i, cs⦄ ≘ i2 → i1 = i2.
#cs #i #i1 #H elim H -cs -i -i1
[ #i #x #H <(at_inv_nil … H) -x //
| #cs #l #m #i #i1 #Hil #_ #IHi1 #x #H
  lapply (at_inv_cons_lt … H Hil) -H -Hil /2 width=1 by/
| #cs #l #m #i #i1 #Hli #_ #IHi1 #x #H
  lapply (at_inv_cons_ge … H Hli) -H -Hli /2 width=1 by/
]
qed-.
