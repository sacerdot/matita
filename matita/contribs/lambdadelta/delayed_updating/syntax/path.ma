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
include "ground/notation/functions/element_e_0.ma".
include "ground/notation/functions/black_circle_2.ma".
include "ground/notation/functions/black_halfcircleright_2.ma".
include "ground/notation/functions/black_halfcircleleft_2.ma".
include "delayed_updating/syntax/label.ma".

(* PATH *********************************************************************)

definition path ≝ list label.

interpretation
  "empty (paths)"
  'ElementE = (list_empty label).

interpretation
  "left cons (paths)"
  'BlackHalfCircleRight l p = (list_lcons label l p).

interpretation
  "append (paths)"
  'BlackCircle l1 l2 = (list_append label l1 l2).

interpretation
  "right cons (paths)"
  'BlackHalfCircleLeft p l = (list_append label p (list_lcons label l (list_empty label))).
