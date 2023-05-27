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

include "ground/relocation/trz_pnext.ma".
include "ground/arith/int_pred_succ.ma".
include "ground/notation/functions/upspoon_1.ma".

(* PUSH FOR TOTAL RELOCATION MAPS WITH INTEGERS *****************************)

definition trz_push_staff (f) (z): ℤ ≝
           zsplit … (λp.(↑⁺f)＠⧣❨↑−p❩) (⁤𝟏) (λp.(↑⁺f)＠⧣❨⁤p❩) (↓z).

(* Constructions with trz_push_staff ******************************************)

lemma trz_push_staff_neg (f) (p):
      (↑⁺f)＠⧣❨−p❩ = trz_push_staff f (−p).
// qed.

lemma trz_push_staff_zero (f):
      (↑⁺f)＠⧣❨𝟎❩ = trz_push_staff f (𝟎).
// qed.

lemma trz_push_staff_pos_unit (f):
      (⁤𝟏) = trz_push_staff f (⁤𝟏).
// qed.

lemma trz_push_staff_pos_succ (f) (p):
      (↑⁺f)＠⧣❨⁤p❩ = trz_push_staff f (⁤↑p).
// qed.

(* Definition of trz_push ***************************************************)

definition trz_push (f:trz_map): trz_map ≝ mk_trz_map ….
[ @(trz_push_staff f)
| * [ #p1 || * [| #p1 ]]
  * [1,4,7,10: #p2 |2,5,8,11:|*: * [1,3,5,7:|*: #p2 ]]
  [ <trz_push_staff_neg <trz_push_staff_neg
    /2 width=2 by trz_injective/
  | <trz_push_staff_zero <trz_push_staff_neg
    /2 width=2 by trz_injective/
  | <trz_push_staff_pos_unit <trz_push_staff_neg
    #H0 elim (eq_inv_pos_unit_trz_puni_staff … H0)
  | <trz_push_staff_pos_succ <trz_push_staff_neg
    #H0 lapply (trz_injective … H0) -H0
    #H0 destruct
  | <trz_push_staff_neg <trz_push_staff_zero
    /2 width=2 by trz_injective/
  | //
  | <trz_push_staff_pos_unit <trz_push_staff_zero
    #H0 elim (eq_inv_pos_unit_trz_puni_staff … H0)
  | <trz_push_staff_pos_succ <trz_push_staff_zero
    #H0 lapply (trz_injective … H0) -H0
    #H0 destruct
  | <trz_push_staff_neg <trz_push_staff_pos_unit
    #H0 elim (eq_inv_trz_puni_staff_pos_unit … H0)
  | <trz_push_staff_zero <trz_push_staff_pos_unit
    #H0 elim (eq_inv_trz_puni_staff_pos_unit … H0)
  | //
  | <trz_push_staff_pos_succ <trz_push_staff_pos_unit
    #H0 elim (eq_inv_trz_puni_staff_pos_unit … H0)
  | <trz_push_staff_neg <trz_push_staff_pos_succ
    #H0 lapply (trz_injective … H0) -H0
    #H0 destruct
  | <trz_push_staff_zero <trz_push_staff_pos_succ
    #H0 lapply (trz_injective … H0) -H0
    #H0 destruct
  | <trz_push_staff_pos_unit <trz_push_staff_pos_succ
    #H0 elim (eq_inv_pos_unit_trz_puni_staff … H0)
  | <trz_push_staff_pos_succ <trz_push_staff_pos_succ
    #H0 lapply (trz_injective … H0) -H0
    #H0 destruct //
  ]
]
defined.

interpretation
  "push (total relocation maps with integers)"
  'UpSpoon f = (trz_push f).

(* Basic constructions ******************************************************)

lemma trz_push_neg (f) (p):
      (↑⁺f)＠⧣❨−p❩ = (⫯f)＠⧣❨−p❩.
// qed.

lemma trz_push_zero (f):
      (↑⁺f)＠⧣❨𝟎❩ = (⫯f)＠⧣❨𝟎❩.
// qed.

lemma trz_push_pos_unit (f):
      (⁤𝟏) = (⫯f)＠⧣❨⁤𝟏❩.
// qed.

lemma trz_push_pos_succ (f) (p):
      (↑⁺f)＠⧣❨⁤p❩ = (⫯f)＠⧣❨⁤↑p❩.
// qed.

(* Advanced constructions ***************************************************)

lemma trz_push_eq_repl_fwd:
      compatible_2_fwd … trz_eq trz_eq trz_push.
#f1 #f2 #Hf * [ #p || * [| #p ]]
/2 width=1 by trz_after_eq_repl/
qed.

lemma trz_after_push_pnext (f2) (f1):
      ↑⁺(f2•f1) ≐ ⫯f2•↑⁺f1.
#f2 #f1 #z
>trz_after_pnext_sn
<trz_after_dapp <trz_after_dapp <trz_after_dapp <trz_after_dapp
generalize in match (f1＠⧣❨z❩); -f1 -z
* [2:|*: #p ] //
qed.

lemma trz_after_push_bi (f2) (f1):
      (⫯(f2•f1)) ≐ (⫯f2)•(⫯f1).
#f2 #f1 * [ #p || * [| #p ]]
<trz_after_dapp
[ <trz_push_neg <trz_push_neg //
| <trz_push_zero <trz_push_zero //
| //
| <trz_push_pos_succ <trz_push_pos_succ //
]
qed.
