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

include "delayed_updating/substitution/lift_gen_eq.ma".
include "delayed_updating/substitution/prelift_label.ma".
include "delayed_updating/substitution/prelift_rmap.ma".

(* LIFT FOR PATH ************************************************************)

(* Constructions with prelift_rmap and prelift_path *************************)

lemma lift_path_lcons_prelift (f) (p) (l):
      (↑[f]l)◗↑[↑[l]f]p = ↑[f](l◗p).
#f #p * [ #n ] //
qed.

lemma lift_path_rcons_prelift (f) (p) (l):
      (↑[f]p)◖↑[↑[p]f]l = ↑[f](p◖l).
#f #p * [ #n ] //
qed.
