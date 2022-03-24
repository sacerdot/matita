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

include "delayed_updating/unwind1/unwind.ma".
include "delayed_updating/syntax/prototerm.ma".
include "ground/lib/subset_ext.ma".

(* UNWIND FOR PROTOTERM *****************************************************)

interpretation
  "unwind (prototerm)"
  'BlackDownTriangle f t = (subset_ext_f1 ? ? (unwind_gen ? proj_path f) t).

(* Basic constructions ******************************************************)

lemma in_comp_unwind_bi (f) (p) (t):
      p ϵ t → ▼[f]p ϵ ▼[f]t.
/2 width=1 by subset_in_ext_f1_dx/
qed.
