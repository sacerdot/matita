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

include "delayed_updating/syntax/prototerm_proper.ma".
include "delayed_updating/syntax/path_inner_proper.ma".
include "ground/lib/subset_overlap.ma".

(* PROPER CONDITION FOR PROTOTERM *******************************************)

(* Constructions with pic ***************************************************)

lemma term_proper_outer (t):
      t ⧸≬ 𝐈 → t ϵ 𝐏.
/4 width=3 by path_des_outer_proper, subset_ol_i/
qed.
