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

include "ground/lib/list_rcons.ma".
include "ground/relocation/fu/ur_item.ma".
include "ground/notation/relations/category_fu_0.ma".
include "ground/notation/functions/element_i_0.ma".
include "ground/notation/functions/black_circle_2.ma".
include "ground/notation/functions/black_halfcircleright_2.ma".
include "ground/notation/functions/black_halfcircleleft_2.ma".
include "ground/notation/functions/upspoon_1.ma".
include "ground/notation/functions/rightuparrowstar_2.ma".

(* FINITE RELOCATION MAPS FOR UNWIND ****************************************)

(* Note: relocation is a list of items *)
(* Note: constructed from the first to be applied (right end) to the last (left end) *)
definition fur_map ≝ list (𝕌𝕀).

interpretation
  "finite relocation maps for unwind"
  'CategoryFU = (fur_map).

interpretation
  "identity (finite relocation maps for unwind)"
  'ElementI = (list_empty ur_item).

interpretation
  "right cons (finite relocation maps for unwind)"
  'BlackHalfCircleLeft f i = (list_lcons ur_item i f).

interpretation
  "append (finite relocation maps for unwind)"
  'BlackCircle g f = (list_append ur_item f g).

interpretation
  "left cons (finite relocation maps for unwind)"
  'BlackHalfCircleRight i f = (list_append ur_item f (list_lcons ur_item i (list_empty ur_item))).

interpretation
  "push (finite relocation maps for unwind)"
  'UpSpoon f = (list_lcons ur_item ur_p f).

interpretation
  "iterated join (finite relocation maps for unwind)"
  'RightUpArrowStar n f = (list_lcons ur_item (ur_j n) f).
