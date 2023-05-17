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

include "ground/arith/pnat_split.ma".
include "ground/arith/int_split.ma".

(* SUCCESSOR INTEGERS *******************************************************)

definition zsucc (z): ℤ ≝
           zsplit ? (psplit … (𝟎) zneg) (𝟏) psucc z.

interpretation
  "successor (integers)"
  'UpArrow z = (zsucc z).

(* Basic constructions ******************************************************)

lemma zsucc_neg_succ (p): zneg p = ↑(zneg (↑p)).
// qed.

lemma zsucc_neg_unit: (𝟎) = ↑(zneg (𝟏)).
// qed.

lemma zsucc_zero: (𝟏) ={ℤ} ↑𝟎.
// qed.

lemma zsucc_pos (p): (↑p) ={ℤ} ↑(zpos p).
// qed.

(* Basic inversions *********************************************************)

lemma eq_inv_zsucc_bi: injective … zsucc.
* [2: |*: #p1 ] * [2,5,8: |*: #p2 ]
[1  :  //
|2,7: cases p1 -p1 [1,3: <zsucc_neg_unit |*: #p1 <zsucc_neg_succ ]
|3,5: <zsucc_pos <zsucc_zero #H0 destruct
|4,8: cases p2 -p2 [1,3: <zsucc_neg_unit |*: #p2 <zsucc_neg_succ ]
|6  : cases p1 -p1 [ <zsucc_neg_unit | #p1 <zsucc_neg_succ ]
      cases p2 -p2 [1,3: <zsucc_neg_unit |*: #p2 <zsucc_neg_succ ] //
|9  : <zsucc_pos <zsucc_pos #H0 destruct //
]
[1,3,5,7: <zsucc_zero #H0 destruct
|2,4,6,8: <zsucc_pos #H0 destruct
|9,10,11: #H0 destruct //
]
qed-.

lemma eq_inv_fix_zsucc (z:ℤ): z = ↑z → ⊥.
* [ * [| #p ] || #p ]
[ <zsucc_neg_unit #H0 destruct
| <zsucc_neg_succ #H0
  /3 width=2 by eq_inv_zneg_bi, eq_inv_fix_psucc/
| <zsucc_zero #H0 destruct
| <zsucc_pos #H0
  /3 width=2 by eq_inv_zpos_bi, eq_inv_fix_psucc/
]
qed-.
