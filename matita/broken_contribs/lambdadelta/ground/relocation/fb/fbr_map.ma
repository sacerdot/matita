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

include "ground/relocation/fb/br_item.ma".
include "ground/lib/list_rcons.ma".
include "ground/notation/relations/category_fb_0.ma".
include "ground/notation/functions/element_i_0.ma".
include "ground/notation/functions/black_circle_2.ma".
include "ground/notation/functions/black_halfcircleright_2.ma".
include "ground/notation/functions/black_halfcircleleft_2.ma".
include "ground/notation/functions/upspoon_1.ma".
include "ground/notation/functions/uparrow_1.ma".

(* FINITE RELOCATION MAPS WITH BOOLEANS *************************************)

(* Note: relocation is a list of items *)
(* Note: constructed from the first to be applied (right end) to the last (left end) *)
definition fbr_map ≝ list (𝔹𝕀).

interpretation
  "finite relocation maps with booleans"
  'CategoryFB = (fbr_map).

interpretation
  "identity (finite relocation maps with booleans)"
  'ElementI = (list_empty br_item).

interpretation
  "right cons (finite relocation maps with booleans)"
  'BlackHalfCircleLeft f i = (list_lcons br_item i f).

interpretation
  "append (finite relocation maps with booleans)"
  'BlackCircle g f = (list_append br_item f g).

interpretation
  "left cons (finite relocation maps with booleans)"
  'BlackHalfCircleRight i f = (list_append br_item f (list_lcons br_item i (list_empty br_item))).

interpretation
  "push (finite relocation maps with booleans)"
  'UpSpoon f = (list_lcons br_item false f).

interpretation
  "next (finite relocation maps with booleans)"
  'UpArrow f = (list_lcons br_item true f).
