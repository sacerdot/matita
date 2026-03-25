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

include "delayed_updating/syntax/path_root_le_clear.ma".
include "delayed_updating/syntax/path_root_eq.ma".

(* ROOT EQUIVALENCE FOR PATH ************************************************)

(* Constructions with path_clear ********************************************)

lemma path_req_clear_bi (p1) (p2):
      p1 ≚ p2 → ⓪p1 ≚ ⓪p2.
#p1 #p2 * #Hp
/3 width=1 by path_req_mk_ge, path_req_mk_le, path_rle_clear_bi/
qed.
