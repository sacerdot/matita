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

include "ground/relocation/tz/tzr_map.ma".
include "ground/arith/int_pred.ma".
include "ground/notation/functions/element_u_plus_0.ma".

(* POSITIVE UNIFORM ELEMENTS FOR TOTAL RELOCATION MAPS WITH INTEGERS ********)

definition tzr_puni_staff: ℤ → ℤ ≝
           zsplit (ℤ) zneg (𝟎) (zpos∘psucc).

(* Constructions with tzr_puni_staff ****************************************)

lemma tzr_puni_staff_neg (p):
      −p = tzr_puni_staff (−p).
// qed.

lemma tzr_puni_staff_zero:
      (𝟎) = tzr_puni_staff (𝟎).
// qed.

lemma tzr_puni_staff_pos (p):
      (⁤↑p) = tzr_puni_staff (⁤p).
// qed.

(* Inversions with tzr_puni_staff *******************************************)

lemma eq_inv_pos_unit_tzr_puni_staff (z):
      (⁤𝟏) = tzr_puni_staff z → ⊥.
* [2:|*: #p ] #H0
[ @(eq_inv_zpos_zero … H0)
| @(eq_inv_zpos_neg … H0)
| lapply (eq_inv_zpos_bi … H0) -H0
  #H0 destruct
]
qed-.

lemma eq_inv_tzr_puni_staff_pos_unit (z):
      tzr_puni_staff z = (⁤𝟏) → ⊥.
* [2:|*: #p ] #H0
[ @(eq_inv_zzero_pos … H0)
| @(eq_inv_zneg_pos … H0)
| lapply (eq_inv_zpos_bi … H0) -H0
  #H0 destruct
]
qed-.

(* Definition for tzr_puni **************************************************)

definition tzr_puni: tzr_map ≝ mk_tzr_map ….
[ @tzr_puni_staff
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
  'ElementUPlus = (tzr_puni).

(* Basic constructions ******************************************************)

lemma tzr_puni_dapp_neg (p):
      −p = 𝐮⁺＠⧣❨−p❩.
// qed.

lemma tzr_puni_dapp_zero:
      (𝟎) = 𝐮⁺＠⧣❨𝟎❩.
// qed.

lemma tzr_puni_dap_pos (p):
      (⁤↑p) = 𝐮⁺＠⧣❨⁤p❩.
// qed.

(* Basic inversions *********************************************************)

lemma eq_inv_pos_unit_tzr_puni_dapp (z):
      (⁤𝟏) = 𝐮⁺＠⧣❨z❩ → ⊥.
@eq_inv_pos_unit_tzr_puni_staff
qed-.

lemma eq_inv_tzr_puni_dapp_pos_unit (z):
      (𝐮⁺)＠⧣❨z❩ = (⁤𝟏) → ⊥.
@eq_inv_tzr_puni_staff_pos_unit
qed-.
