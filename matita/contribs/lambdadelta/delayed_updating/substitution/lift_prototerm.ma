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
include "delayed_updating/syntax/prototerm.ma".
include "ground/lib/subset_ext.ma".

(* LIFT FOR PROTOTERM *******************************************************)

interpretation
  "lift (prototerm)"
  'UpArrow f t = (subset_ext_f1 ? ? (lift_path f) t).

(* Basic constructions ******************************************************)

lemma in_comp_lift_path_term (f) (t) (p):
      p ϵ t → ↑[f]p ϵ ↑[f]t.
/2 width=1 by subset_in_ext_f1_dx/
qed.
