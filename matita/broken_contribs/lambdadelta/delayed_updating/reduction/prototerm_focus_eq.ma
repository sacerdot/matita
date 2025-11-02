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

include "ground/subsets/subset_and_le.ma".
include "delayed_updating/reduction/prototerm_focus.ma".

(* BALANCED REDUCTION EXTENDED FOCUS ****************************************)

(* Constructions with term_le ***********************************************)

lemma term_focus_le (t) (p) (b) (q) (n):
      (𝐅❨t,p,b,q,n❩) ⊆ t.
/2 width=2 by subset_le_and_sx_refl_sx/
qed.
