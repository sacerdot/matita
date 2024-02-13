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

include "delayed_updating/syntax/path_le.ma".
include "delayed_updating/syntax/prototerm_clear.ma".

(* ROOT ORDER FOR PATH ******************************************************)

(* Constructions with path_clear ********************************************)

lemma path_le_clear_bi (p1) (p2):
      p1 ⊑ p2 → ⓪p1 ⊑ ⓪p2.
/2 width=1 by term_slice_clear/
qed.
