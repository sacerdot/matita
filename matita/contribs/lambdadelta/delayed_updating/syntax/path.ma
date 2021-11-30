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

include "ground/lib/list.ma".
include "delayed_updating/notation/functions/element_e_0.ma".
include "delayed_updating/syntax/label.ma".

(* PATH *********************************************************************)

definition path ≝ list label.

interpretation
  "empty (paths)"
  'ElementE = (list_nil label).
