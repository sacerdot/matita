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
include "delayed_updating/syntax/path_depth.ma".
include "ground/relocation/tr_pushs.ma".

(* LIFT FOR PATH ***********************************************************)

(* Basic constructions with depth ******************************************)

lemma pippo (p) (f):
      (⫯*[❘p❘]f) ∘ (↑[p]𝐢) = ↑[p]f.
#p elim p -p
[ #f <lift_rmap_empty <lift_rmap_empty <tr_pushs_zero
| * [ #n ] #p #IH #f //
  <lift_rmap_d_sn <lift_rmap_d_sn <depth_d
  @(trans_eq … (IH …)) -IH
      
