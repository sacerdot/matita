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
include "ground/notation/functions/double_semicolon_2.ma".
include "delayed_updating/syntax/label.ma".
include "delayed_updating/notation/functions/semicolon_2.ma".
include "delayed_updating/notation/functions/comma_2.ma".


(* PATH *********************************************************************)

definition path ≝ list label.

interpretation
  "empty (paths)"
  'ElementE = (list_empty label).

interpretation
  "left cons (paths)"
  'Semicolon l p = (list_lcons label l p).

interpretation
  "append (paths)"
  'DoubleSemicolon l1 l2 = (list_append label l1 l2).

interpretation
  "right cons (paths)"
  'Comma p l = (list_append label p (list_lcons label l (list_empty label))).
