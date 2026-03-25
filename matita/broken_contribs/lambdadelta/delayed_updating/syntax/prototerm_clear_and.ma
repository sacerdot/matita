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
include "ground/subsets/subset_and.ma".
include "delayed_updating/syntax/prototerm_clear.ma".

(* CLEARED PROTOTERM ********************************************************)

(* Constructions with subset_and and subset_le ******************************)

(* Note: the other inclusion does not hold as is *)
lemma clear_and_le (t1) (t2):
      ⓪(t1 ∩ t2) ⊆ (⓪t1) ∩ (⓪t2).
#t1 #t2 #p0 * #p * #H1p #H2p #H0 destruct
/3 width=1 by in_comp_term_clear, subset_and_in/
qed.
