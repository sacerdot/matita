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

include "delayed_updating/substitution/lift_path_eq.ma".
include "ground/relocation/fb/fbr_uni_ctls.ma".

(* LIFT FOR PATH ************************************************************)

(* Constructions with map_uni ***********************************************)

lemma lift_path_d_sx_pos_uni (p) (n) (k):
      (𝗱((⁤k)+n)◗p) = 🠡[𝐮❨n❩](𝗱(⁤k)◗p).
// qed.
