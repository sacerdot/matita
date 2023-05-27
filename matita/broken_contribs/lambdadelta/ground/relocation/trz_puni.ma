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

include "ground/relocation/trz_map.ma".
include "ground/arith/int_pred.ma".
include "ground/notation/functions/element_u_plus_0.ma".
include "ground/notation/functions/uparrowplus_1.ma".

(* POSITIVE UNIFORM ELEMENTS FOR TOTAL RELOCATION MAPS WITH INTEGERS ********)

definition trz_puni_staff: ℤ → ℤ ≝
           zsplit (ℤ) zneg (𝟎) (zpos∘psucc).

(* Constructions with trz_puni_staff ****************************************)

lemma trz_puni_staff_neg (p):
      −p = trz_puni_staff (−p).
// qed.

lemma trz_puni_staff_zero:
      (𝟎) = trz_puni_staff (𝟎).
// qed.

lemma trz_puni_staff_pos (p):
      (⁤↑p) = trz_puni_staff (⁤p).
// qed.

(* Inversions with trz_puni_staff *******************************************)

lemma eq_inv_pos_unit_trz_puni_staff (z):
      (⁤𝟏) = trz_puni_staff z → ⊥.
* [2:|*: #p ] #H0
[ @(eq_inv_zpos_zero … H0)
| @(eq_inv_zpos_neg … H0)
| lapply (eq_inv_zpos_bi … H0) -H0
  #H0 destruct
]
qed-.

lemma eq_inv_trz_puni_staff_pos_unit (z):
      trz_puni_staff z = (⁤𝟏) → ⊥.
* [2:|*: #p ] #H0
[ @(eq_inv_zzero_pos … H0)
| @(eq_inv_zneg_pos … H0)
| lapply (eq_inv_zpos_bi … H0) -H0
  #H0 destruct
]
qed-.

(* Definition for trz_puni **************************************************)

definition trz_puni: trz_map ≝ mk_trz_map ….
[ @trz_puni_staff
| * [2:|*: #p1 ] * [2,5,8:|*: #p2 ] // #H0
  [ elim (eq_inv_zpos_zero … H0)
  | elim (eq_inv_zzero_pos … H0)
  | elim (eq_inv_zneg_pos … H0)
  | elim (eq_inv_zpos_neg … H0)
  ]
]
defined.

interpretation
  "positive uniform elements (total relocation maps with integer)"
  'ElementUPlus = (trz_puni).

(* Basic constructions ******************************************************)

lemma trz_puni_neg (p):
      −p = 𝐮⁺＠⧣❨−p❩.
// qed.

lemma trz_puni_zero:
      (𝟎) = 𝐮⁺＠⧣❨𝟎❩.
// qed.

lemma trz_puni_pos (p):
      (⁤↑p) = 𝐮⁺＠⧣❨⁤p❩.
// qed.

(* Basic inversions *********************************************************)

lemma eq_inv_pos_unit_trz_puni (z):
      (⁤𝟏) = 𝐮⁺＠⧣❨z❩ → ⊥.
@eq_inv_pos_unit_trz_puni_staff
qed-.

lemma eq_inv_trz_puni_pos_unit (z):
      (𝐮⁺)＠⧣❨z❩ = (⁤𝟏) → ⊥.
@eq_inv_trz_puni_staff_pos_unit
qed-.
