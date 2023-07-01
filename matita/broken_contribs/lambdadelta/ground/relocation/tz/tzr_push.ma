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

include "ground/relocation/tz/tzr_pnext.ma".
include "ground/arith/int_pred_succ.ma".
include "ground/notation/functions/upspoon_1.ma".

(* PUSH FOR TOTAL RELOCATION MAPS WITH INTEGERS *****************************)

definition tzr_push_staff (f) (z): ℤ ≝
           zsplit … (λp.(↑⁺f)＠⧣❨↑−p❩) (⁤𝟏) (λp.(↑⁺f)＠⧣❨⁤p❩) (↓z).

(* Constructions with tzr_push_staff ******************************************)

lemma tzr_push_staff_dapp_neg (f) (p):
      (↑⁺f)＠⧣❨−p❩ = tzr_push_staff f (−p).
// qed.

lemma tzr_push_staff_dapp_zero (f):
      (↑⁺f)＠⧣❨𝟎❩ = tzr_push_staff f (𝟎).
// qed.

lemma tzr_push_staff_pos_unit (f):
      (⁤𝟏) = tzr_push_staff f (⁤𝟏).
// qed.

lemma tzr_push_staff_dapp_pos_succ (f) (p):
      (↑⁺f)＠⧣❨⁤p❩ = tzr_push_staff f (⁤↑p).
// qed.

(* Definition of tzr_push ***************************************************)

definition tzr_push (f:tzr_map): tzr_map ≝ mk_tzr_map ….
[ @(tzr_push_staff f)
| * [ #p1 || * [| #p1 ]]
  * [1,4,7,10: #p2 |2,5,8,11:|*: * [1,3,5,7:|*: #p2 ]]
  [ <tzr_push_staff_dapp_neg <tzr_push_staff_dapp_neg
    /2 width=2 by tzr_injective/
  | <tzr_push_staff_dapp_zero <tzr_push_staff_dapp_neg
    /2 width=2 by tzr_injective/
  | <tzr_push_staff_pos_unit <tzr_push_staff_dapp_neg
    #H0 elim (eq_inv_pos_unit_tzr_puni_staff … H0)
  | <tzr_push_staff_dapp_pos_succ <tzr_push_staff_dapp_neg
    #H0 lapply (tzr_injective … H0) -H0
    #H0 destruct
  | <tzr_push_staff_dapp_neg <tzr_push_staff_dapp_zero
    /2 width=2 by tzr_injective/
  | //
  | <tzr_push_staff_pos_unit <tzr_push_staff_dapp_zero
    #H0 elim (eq_inv_pos_unit_tzr_puni_staff … H0)
  | <tzr_push_staff_dapp_pos_succ <tzr_push_staff_dapp_zero
    #H0 lapply (tzr_injective … H0) -H0
    #H0 destruct
  | <tzr_push_staff_dapp_neg <tzr_push_staff_pos_unit
    #H0 elim (eq_inv_tzr_puni_staff_pos_unit … H0)
  | <tzr_push_staff_dapp_zero <tzr_push_staff_pos_unit
    #H0 elim (eq_inv_tzr_puni_staff_pos_unit … H0)
  | //
  | <tzr_push_staff_dapp_pos_succ <tzr_push_staff_pos_unit
    #H0 elim (eq_inv_tzr_puni_staff_pos_unit … H0)
  | <tzr_push_staff_dapp_neg <tzr_push_staff_dapp_pos_succ
    #H0 lapply (tzr_injective … H0) -H0
    #H0 destruct
  | <tzr_push_staff_dapp_zero <tzr_push_staff_dapp_pos_succ
    #H0 lapply (tzr_injective … H0) -H0
    #H0 destruct
  | <tzr_push_staff_pos_unit <tzr_push_staff_dapp_pos_succ
    #H0 elim (eq_inv_pos_unit_tzr_puni_staff … H0)
  | <tzr_push_staff_dapp_pos_succ <tzr_push_staff_dapp_pos_succ
    #H0 lapply (tzr_injective … H0) -H0
    #H0 destruct //
  ]
]
defined.

interpretation
  "push (total relocation maps with integers)"
  'UpSpoon f = (tzr_push f).

(* Basic constructions ******************************************************)

lemma tzr_push_dapp_neg (f) (p):
      (↑⁺f)＠⧣❨−p❩ = (⫯f)＠⧣❨−p❩.
// qed.

lemma tzr_push_dapp_zero (f):
      (↑⁺f)＠⧣❨𝟎❩ = (⫯f)＠⧣❨𝟎❩.
// qed.

lemma tzr_push_dapp_pos_unit (f):
      (⁤𝟏) = (⫯f)＠⧣❨⁤𝟏❩.
// qed.

lemma tzr_push_dapp_pos_succ (f) (p):
      (↑⁺f)＠⧣❨⁤p❩ = (⫯f)＠⧣❨⁤↑p❩.
// qed.

(* Advanced constructions ***************************************************)

lemma tzr_push_eq_repl:
      compatible_2_fwd … tzr_eq tzr_eq (λf.⫯f).
#f1 #f2 #Hf * [ #p || * [| #p ]]
/2 width=1 by tzr_after_eq_repl/
qed.

lemma tzr_after_push_pnext (f2) (f1):
      ↑⁺(f2•f1) ≐ ⫯f2•↑⁺f1.
#f2 #f1 #z
>tzr_after_pnext_sn
<tzr_after_dapp <tzr_after_dapp <tzr_after_dapp <tzr_after_dapp
generalize in match (f1＠⧣❨z❩); -f1 -z
* [2:|*: #p ] //
qed.

theorem tzr_after_push_bi (f2) (f1):
        (⫯(f2•f1)) ≐ (⫯f2)•(⫯f1).
#f2 #f1 * [ #p || * [| #p ]]
<tzr_after_dapp
[ <tzr_push_dapp_neg <tzr_push_dapp_neg //
| <tzr_push_dapp_zero <tzr_push_dapp_zero //
| //
| <tzr_push_dapp_pos_succ <tzr_push_dapp_pos_succ //
]
qed.
