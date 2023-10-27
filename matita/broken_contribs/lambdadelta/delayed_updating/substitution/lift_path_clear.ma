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

include "delayed_updating/substitution/lift_path.ma".
include "delayed_updating/syntax/path_clear.ma".

(* LIFT FOR PATH ************************************************************)

(* Constructions with path_clear ********************************************)

lemma clear_lift_path (f) (p):
      ⓪p = ⓪🠡[f]p.
#f #p elim p -p //
* [ #k ] #p #IH //
<path_clear_d_dx <lift_path_d_dx //
qed.

lemma lift_path_clear (f) (p):
      ⓪p = 🠡[f]⓪p.
#f #p elim p -p //
* [ #k ] #p #IH //
<path_clear_d_dx <lift_path_d_dx //
qed.

lemma lift_path_clear_swap (f) (p):
      ⓪🠡[f]p = 🠡[f]⓪p.
// qed-.
