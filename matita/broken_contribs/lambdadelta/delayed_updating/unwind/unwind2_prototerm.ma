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

include "delayed_updating/unwind/unwind2_path.ma".
include "delayed_updating/syntax/prototerm.ma".
include "ground/subsets/subset_ext.ma".

(* TAILED UNWIND FOR PROTOTERM **********************************************)

interpretation
  "unwind (prototerm)"
  'BlackDownTriangle f t = (subset_ext_f1 ? ? (unwind2_path f) t).

(* Basic constructions ******************************************************)

lemma in_comp_unwind2_bi (f) (p) (t):
      p ϵ t → ▼[f]p ϵ ▼[f]t.
/2 width=1 by subset_in_ext_f1_dx/
qed.
