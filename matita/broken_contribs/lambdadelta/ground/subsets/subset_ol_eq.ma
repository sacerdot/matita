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

include "ground/subsets/subset_eq.ma".
include "ground/subsets/subset_ol_le.ma".

(* OVERLAP FOR SUBSETS ******************************************************)

(* Constructions with subset_eq *********************************************)

lemma subset_ol_eq_repl (A):
      replace_2 … (subset_eq …) (subset_eq …) (subset_ol A).
#A #u1 #v1 #H1 #u2 * #H2 #_ #v2 * #H3 #_
/2 width=5 by subset_ol_le_repl/
qed.
