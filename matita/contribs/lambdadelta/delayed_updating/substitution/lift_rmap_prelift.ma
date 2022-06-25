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

include "delayed_updating/substitution/lift_gen.ma".
include "delayed_updating/substitution/prelift_rmap.ma".

(* LIFT FOR RELOCATION MAP **************************************************)

(* Constructions with prelift_rmap ******************************************)

lemma lift_rmap_lcons_prelift (f) (p) (l):
      ↑[p]↑[l]f = ↑[l◗p]f.
#f #p * [ #n ] //
qed.

lemma lift_rmap_rcons_prelift (f) (p) (l):
      ↑[l]↑[p]f = ↑[p◖l]f.
#f #p * [ #n ] //
qed.
