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

include "ground/arith/int_split.ma".
include "ground/arith/pnat_split.ma".
include "ground/notation/functions/downarrow_1.ma".

(* PREDECESSOR FOR INTEGERS *************************************************)

definition zpred (z): ℤ ≝
           zsplit ? (zneg∘psucc) (zneg (𝟏)) (psplit … (𝟎) zpos) z.

interpretation
  "predecessor (integers)"
  'DownArrow z = (zpred z).

(* Basic constructions ******************************************************)

lemma zpred_neg (p): −↑p = ↓−p.
// qed.

lemma zpred_zero: −𝟏 = ↓𝟎.
// qed.

lemma zpred_pos_unit: (𝟎) = ↓⁤𝟏.
// qed.

lemma zpred_pos_succ (p): (⁤p) = ↓⁤↑p.
// qed.

(* Basic inversions *********************************************************)

lemma eq_inv_zpred_bi: injective … zpred.
* [2: |*: #p1 ] * [2,5,8: |*: #p2 ]
[1  :  //
|2,4: <zpred_neg <zpred_zero #H0 destruct
|3,8: cases p1 -p1 [1,3: <zpred_pos_unit |*: #p1 <zpred_pos_succ ]
|5,7: cases p2 -p2 [1,3: <zpred_pos_unit |*: #p2 <zpred_pos_succ ]
|6  : <zpred_neg <zpred_neg #H0 destruct //
|9  : cases p1 -p1 [ <zpred_pos_unit | #p1 <zpred_pos_succ ]
      cases p2 -p2 [1,3: <zpred_pos_unit |*: #p2 <zpred_pos_succ ] //
]
[1,3,5,7: <zpred_zero #H0 destruct
|2,4,6,8: <zpred_neg #H0 destruct
|9,10,11: #H0 destruct //
]
qed-.

lemma eq_inv_self_zpred (z): z = ↓z → ⊥.
* [ #p || * [| #p ]]
[ <zpred_neg #H0
  /3 width=2 by eq_inv_zneg_bi, eq_inv_refl_psucc/
| <zpred_zero #H0 destruct
| <zpred_pos_unit #H0 destruct
| <zpred_pos_succ #H0
  /3 width=2 by eq_inv_zpos_bi, eq_inv_refl_psucc/
]
qed-.
