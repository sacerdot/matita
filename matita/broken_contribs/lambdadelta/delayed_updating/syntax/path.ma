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

(* Note: a path is a list of labels *)
(* Note: constructed from the leaf (right end) to the root (left end) *)
definition path ≝ list label.

interpretation
  "empty (paths)"
  'ElementE = (list_empty label).

interpretation
  "right cons (paths)"
  'BlackHalfCircleLeft p l = (list_lcons label l p).

interpretation
  "append (paths)"
  'BlackCircle p q = (list_append label q p).

interpretation
  "left cons (paths)"
  'BlackHalfCircleRight l p = (list_append label p (list_lcons label l (list_empty label))).

(* Helper constructions *****************************************************)

lemma path_append_append_lcons (p) (q) (r) (l):
      p●(r◖l)●q = p●r●(l◗q).
// qed-.

lemma path_append_lcons_append (p) (q) (r) (l):
      (p◖l)●r●q = p●(l◗r)●q.
// qed-.
