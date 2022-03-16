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

include "delayed_updating/substitution/lift.ma".
include "delayed_updating/syntax/path_structure.ma".
include "delayed_updating/syntax/path_depth.ma".
include "ground/arith/nat_pred_succ.ma".

(* LIFT FOR PATH ***********************************************************)

(* Basic constructions with structure and depth ****************************)

lemma lift_rmap_structure (p) (f):
      (⫯*[❘p❘]f) = ↑[⊗p]f.
#p elim p -p //
* [ #n ] #p #IH #f //
[ <lift_rmap_A_sn //
| <lift_rmap_S_sn //
]
qed.
