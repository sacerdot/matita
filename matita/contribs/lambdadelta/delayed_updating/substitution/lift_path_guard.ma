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
include "delayed_updating/syntax/path_guard.ma".

(* LIFT FOR PATH ************************************************************)

(* Constructions with pgc ***************************************************)

lemma lift_path_guard (f) (p):
      p ϵ 𝐆 → 🠡[f]p ϵ 𝐆.
#f #p #H0 elim H0 -p //
qed.
