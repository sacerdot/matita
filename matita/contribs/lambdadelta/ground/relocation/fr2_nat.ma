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

include "ground/notation/relations/ratsection_3.ma".
include "ground/arith/nat_plus.ma".
include "ground/arith/nat_lt.ma".
include "ground/relocation/fr2_map.ma".

(* NON-NEGATIVE APPLICATION FOR FINITE RELOCATION MAPS WITH PAIRS ***********)

(*** at *)
inductive fr2_nat: fr2_map â relation nat â
(*** at_nil *)
| fr2_nat_empty (l):
  fr2_nat (ð) l l
(*** at_lt *)
| fr2_nat_lt (f) (d) (h) (l1) (l2):
  l1 < d â fr2_nat f l1 l2 â fr2_nat (â¨d,hâ©âf) l1 l2
(*** at_ge *)
| fr2_nat_ge (f) (d) (h) (l1) (l2):
  d â¤ l1 â fr2_nat f (l1 + h) l2 â fr2_nat (â¨d,hâ©âf) l1 l2
.

interpretation
  "non-negative relational application (finite relocation maps with pairs)"
  'RAtSection l1 f l2 = (fr2_nat f l1 l2).

(* Basic inversions *********************************************************)

(*** at_inv_nil *)
lemma fr2_nat_inv_empty (l1) (l2):
      ï¼ Â§â¨l1, ðâ© â l2 â l1 = l2.
#l1 #l2 @(insert_eq_1 â¦ (ð))
#f * -f -l1 -l2
[ //
| #f #d #h #l1 #l2 #_ #_ #H destruct
| #f #d #h #l1 #l2 #_ #_ #H destruct
]
qed-.

(*** at_inv_cons *)
lemma fr2_nat_inv_lcons (f) (d) (h) (l1) (l2):
      ï¼ Â§â¨l1, â¨d,hâ©âfâ© â l2 â
      â¨â¨ â§â§ l1 < d & ï¼ Â§â¨l1, fâ© â l2 
       | â§â§ d â¤ l1 & ï¼ Â§â¨l1+h, fâ© â l2.
#g #d #h #l1 #l2 @(insert_eq_1 â¦ (â¨d, hâ©âg))
#f * -f -l1 -l2
[ #l #H destruct
| #f1 #d1 #h1 #l1 #l2 #Hld1 #Hl12 #H destruct /3 width=1 by or_introl, conj/
| #f1 #d1 #h1 #l1 #l2 #Hdl1 #Hl12 #H destruct /3 width=1 by or_intror, conj/
]
qed-.

(*** at_inv_cons *)
lemma fr2_nat_inv_lcons_lt (f) (d) (h) (l1) (l2):
      ï¼ Â§â¨l1, â¨d,hâ©âfâ© â l2 â l1 < d â ï¼ Â§â¨l1, fâ© â l2.
#f #d #h #l1 #h2 #H
elim (fr2_nat_inv_lcons â¦ H) -H * // #Hdl1 #_ #Hl1d
elim (nlt_ge_false â¦ Hl1d Hdl1)
qed-.

(*** at_inv_cons *)
lemma fr2_nat_inv_lcons_ge (f) (d) (h) (l1) (l2):
      ï¼ Â§â¨l1, â¨d,hâ©âfâ© â l2 â d â¤ l1 â ï¼ Â§â¨l1+h, fâ© â l2.
#f #d #h #l1 #h2 #H
elim (fr2_nat_inv_lcons â¦ H) -H * // #Hl1d #_ #Hdl1
elim (nlt_ge_false â¦ Hl1d Hdl1)
qed-.
