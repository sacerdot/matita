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

include "ground/xoa/ex_3_1.ma".
include "ground/notation/relations/rminus_3.ma".
include "ground/arith/nat_plus.ma".
include "ground/arith/nat_minus.ma".
include "ground/arith/nat_lt_le.ma".
include "ground/relocation/f2/fr2_map.ma".

(* RELATIONAL SUBTRACTION FOR FINITE RELOCATION MAPS WITH PAIRS *************)

(*** minuss *)
inductive fr2_minus: ℕ → relation2 fr2_map fr2_map ≝
(*** minuss_nil *)
| fr2_minus_empty (i):
  fr2_minus i (𝐞) (𝐞)
(*** minuss_lt *)
| fr2_minus_lt (f1) (f2) (d) (h) (i):
  i < d → fr2_minus i f1 f2 → fr2_minus i (❨d,h❩◗f1) (❨d-i,h❩◗f2)
(*** minuss_ge *)
| fr2_minus_ge (f1) (f2) (d) (h) (i):
  d ≤ i → fr2_minus (h+i) f1 f2 → fr2_minus i (❨d,h❩◗f1) f2
.

interpretation
  "minus (finite relocation maps with pairs)"
  'RMinus f1 i f2 = (fr2_minus i f1 f2).

(* Basic inversions *********************************************************)

(*** minuss_inv_nil1 *)
lemma fr2_minus_inv_empty_sx (f2) (i):
      𝐞 ▭ i ≘ f2 → f2 = 𝐞.
#f2 #i @(insert_eq_1 … (𝐞))
#f1 * -f1 -f2 -i
[ //
| #f1 #f2 #d #h #i #_ #_ #H destruct
| #f1 #f2 #d #h #i #_ #_ #H destruct
]
qed-.

(*** minuss_inv_cons1 *)
lemma fr2_minus_inv_lcons_sx (f1) (f2) (d) (h) (i):
      ❨d, h❩◗f1 ▭ i ≘ f2 →
      ∨∨ ∧∧ d ≤ i & f1 ▭ h+i ≘ f2
       | ∃∃f. i < d & f1 ▭ i ≘ f & f2 = ❨d-i,h❩◗f.
#g1 #f2 #d #h #i @(insert_eq_1 … (❨d,h❩◗g1))
#f1 * -f1 -f2 -i
[ #i #H destruct
| #f1 #f #d1 #h1 #i1 #Hid1 #Hf #H destruct /3 width=3 by ex3_intro, or_intror/
| #f1 #f #d1 #h1 #i1 #Hdi1 #Hf #H destruct /3 width=1 by or_introl, conj/
]
qed-.

(*** minuss_inv_cons1_ge *)
lemma fr2_minus_inv_lcons_sx_ge (f1) (f2) (d) (h) (i):
      ❨d, h❩◗f1 ▭ i ≘ f2 → d ≤ i → f1 ▭ h+i ≘ f2.
#f1 #f2 #d #h #i #H
elim (fr2_minus_inv_lcons_sx … H) -H * // #f #Hid #_ #_ #Hdi
elim (nlt_ge_false … Hid Hdi)
qed-.

(*** minuss_inv_cons1_lt *)
lemma fr2_minus_inv_lcons_sx_lt (f1) (f2) (d) (h) (i):
      ❨d, h❩◗f1 ▭ i ≘ f2 → i < d →
      ∃∃f. f1 ▭ i ≘ f & f2 = ❨d-i,h❩◗f.
#f1 #f2 #d #h #i #H elim (fr2_minus_inv_lcons_sx … H) -H *
[ #Hdi #_ #Hid elim (nlt_ge_false … Hid Hdi)
| /2 width=3 by ex2_intro/
]
qed-.
