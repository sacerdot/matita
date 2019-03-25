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

include "static_2/syntax/tdeq.ma".
include "static_2/syntax/theq.ma".

(* HEAD EQUIVALENCE FOR TERMS ***********************************************)

(* Properties with sort-irrelevant equivalence for terms ********************)

lemma tdeq_theq: ∀T1,T2. T1 ≛ T2 → T1 ⩳ T2.
#T1 #T2 * -T1 -T2 /2 width=1 by theq_sort, theq_pair/
qed.
