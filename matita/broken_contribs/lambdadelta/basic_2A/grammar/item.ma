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

include "ground/lib/bool.ma".
include "ground/lib/arith.ma".

(* ITEMS ********************************************************************)

(* atomic items *)
inductive item0: Type[0] ≝
   | Sort: nat → item0 (* sort: starting at 0 *)
   | LRef: nat → item0 (* reference by index: starting at 0 *)
   | GRef: nat → item0 (* reference by position: starting at 0 *)
.

(* binary binding items *)
inductive bind2: Type[0] ≝
  | Abbr: bind2 (* abbreviation *)
  | Abst: bind2 (* abstraction *)
.

(* binary non-binding items *)
inductive flat2: Type[0] ≝
  | Appl: flat2 (* application *)
  | Cast: flat2 (* explicit type annotation *)
.

(* binary items *)
inductive item2: Type[0] ≝
  | Bind2: bool → bind2 → item2 (* polarized binding item *)
  | Flat2: flat2 → item2        (* non-binding item *)
.

(* Basic inversion lemmas ***************************************************)

fact destruct_sort_sort_aux: ∀k1,k2. Sort k1 = Sort k2 → k1 = k2.
#k1 #k2 #H destruct //
qed-.

(* Basic properties *********************************************************)

lemma eq_item0_dec: ∀I1,I2:item0. Decidable (I1 = I2).
* #i1 * #i2 [2,3,4,6,7,8: @or_intror #H destruct ]
elim (eq_nat_dec i1 i2) /2 width=1 by or_introl/
#Hni12 @or_intror #H destruct /2 width=1 by/
qed-.

lemma eq_bind2_dec: ∀I1,I2:bind2. Decidable (I1 = I2).
* * /2 width=1 by or_introl/
@or_intror #H destruct
qed-.

lemma eq_flat2_dec: ∀I1,I2:flat2. Decidable (I1 = I2).
* * /2 width=1 by or_introl/
@or_intror #H destruct
qed-.

lemma eq_item2_dec: ∀I1,I2:item2. Decidable (I1 = I2).
* [ #a1 ] #I1 * [1,3: #a2 ] #I2
[2,3: @or_intror #H destruct
| elim (eq_bool_dec a1 a2) #Ha
  [ elim (eq_bind2_dec I1 I2) /2 width=1 by or_introl/ #HI ]
  @or_intror #H destruct /2 width=1 by/
| elim (eq_flat2_dec I1 I2) /2 width=1 by or_introl/ #HI
  @or_intror #H destruct /2 width=1 by/
]
qed-.
