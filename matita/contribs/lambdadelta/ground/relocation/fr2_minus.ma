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
include "ground/arith/nat_lt.ma".
include "ground/relocation/fr2_map.ma".

(* RELATIONAL SUBTRACTION FOR FINITE RELOCATION MAPS WITH PAIRS *************)

(*** minuss *)
inductive fr2_minus: nat â relation fr2_map â
(*** minuss_nil *)
| fr2_minus_empty (i):
  fr2_minus i (ð) (ð)
(*** minuss_lt *)
| fr2_minus_lt (f1) (f2) (d) (h) (i):
  i < d â fr2_minus i f1 f2 â fr2_minus i (â¨d,hâ©âf1) (â¨d-i,hâ©âf2)
(*** minuss_ge *)
| fr2_minus_ge (f1) (f2) (d) (h) (i):
  d â¤ i â fr2_minus (h+i) f1 f2 â fr2_minus i (â¨d,hâ©âf1) f2
.

interpretation
  "minus (finite relocation maps with pairs)"
  'RMinus f1 i f2 = (fr2_minus i f1 f2).

(* Basic inversions *********************************************************)

(*** minuss_inv_nil1 *)
lemma fr2_minus_inv_empty_sn (f2) (i):
      ð â­ i â f2 â f2 = ð.
#f2 #i @(insert_eq_1 â¦ (ð))
#f1 * -f1 -f2 -i
[ //
| #f1 #f2 #d #h #i #_ #_ #H destruct
| #f1 #f2 #d #h #i #_ #_ #H destruct
]
qed-.

(*** minuss_inv_cons1 *)
lemma fr2_minus_inv_lcons_sn (f1) (f2) (d) (h) (i):
      â¨d, hâ©âf1 â­ i â f2 â
      â¨â¨ â§â§ d â¤ i & f1 â­ h+i â f2
       | ââf. i < d & f1 â­ i â f & f2 = â¨d-i,hâ©âf.
#g1 #f2 #d #h #i @(insert_eq_1 â¦ (â¨d,hâ©âg1))
#f1 * -f1 -f2 -i
[ #i #H destruct
| #f1 #f #d1 #h1 #i1 #Hid1 #Hf #H destruct /3 width=3 by ex3_intro, or_intror/
| #f1 #f #d1 #h1 #i1 #Hdi1 #Hf #H destruct /3 width=1 by or_introl, conj/
]
qed-.

(*** minuss_inv_cons1_ge *)
lemma fr2_minus_inv_lcons_sn_ge (f1) (f2) (d) (h) (i):
      â¨d, hâ©âf1 â­ i â f2 â d â¤ i â f1 â­ h+i â f2.
#f1 #f2 #d #h #i #H
elim (fr2_minus_inv_lcons_sn â¦ H) -H * // #f #Hid #_ #_ #Hdi
elim (nlt_ge_false â¦ Hid Hdi)
qed-.

(*** minuss_inv_cons1_lt *)
lemma fr2_minus_inv_lcons_sn_lt (f1) (f2) (d) (h) (i):
      â¨d, hâ©âf1 â­ i â f2 â i < d â
      ââf. f1 â­ i â f & f2 = â¨d-i,hâ©âf.
#f1 #f2 #d #h #i #H elim (fr2_minus_inv_lcons_sn â¦ H) -H *
[ #Hdi #_ #Hid elim (nlt_ge_false â¦ Hid Hdi)
| /2 width=3 by ex2_intro/
]
qed-.
