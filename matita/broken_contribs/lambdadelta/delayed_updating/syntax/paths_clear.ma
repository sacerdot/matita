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

include "delayed_updating/syntax/path_clear.ma".

(* CLEAR FOR PATH ***********************************************************)

definition paths_clear (ps) ≝
           list_map … path_clear ps
.

interpretation
  "clear (list of paths)"
  'CircledZero ps = (paths_clear ps).

(* Basic constructions ******************************************************)

lemma paths_clear_unfold (ps):
      list_map … path_clear ps = ⓪ps.
//
qed.

lemma paths_clear_empty:
      (ⓔ) = ⓪ⓔ.
// qed.

lemma paths_clear_lcons (p:ℙ) (qs):
      (⓪p)⨮⓪qs = ⓪(p⨮qs).
//
qed.

(* Main constructions *******************************************************)

theorem paths_clear_append (ps) (qs):
        (⓪ps⨁⓪qs) = ⓪(ps⨁qs).
//
qed.

(* Constructions with list_rcons ********************************************)

lemma paths_clear_rcons (ps) (q:ℙ):
      (⓪ps)⨭⓪q = ⓪(ps⨭q).
// qed.
