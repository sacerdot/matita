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

include "delayed_updating/syntax/path_closed.ma".
include "delayed_updating/syntax/path_height.ma".
include "delayed_updating/syntax/path_depth.ma".

(* CLOSED CONDITION FOR PATH ************************************************)

(* Constructions with height and depth **************************************)

lemma path_closed_depth (p) (n):
      p ϵ 𝐂❨n❩ → ♯p + n = ♭p.
#p #n #Hn elim Hn -Hn //
qed.
