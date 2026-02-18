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

include "ground/subsets/subset_le.ma".
include "ground/subsets/subset_ol.ma".

(* OVERLAP FOR SUBSETS ******************************************************)

(* Constructions with subset_le *********************************************)

lemma subset_ol_le_repl (A):
      replace_2 … (subset_le …) (subset_le …) (subset_ol A).
#A #u1 #v1 * #p1 #H1 #H2 #u2 #Hu #v2 #Hv
/3 width=3 by subset_ol_i/
qed.

(* Negated constructions with subset_le *************************************)

lemma subset_nol_le_repl (A):
      ∀u1,v1. u1 ⧸≬ v1 → ∀u2. u2 ⊆ u1 → ∀v2. v2 ⊆ v1 → u2 ⧸≬❪A❫ v2.
/3 width=5 by subset_ol_le_repl/
qed-.
