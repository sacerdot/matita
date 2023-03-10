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

include "static_2/syntax/teqg.ma".
include "static_2/syntax/teqo.ma".

(* SORT-IRRELEVANT OUTER EQUIVALENCE FOR TERMS ******************************)

(* Properties with generic equivalence for terms ****************************)

lemma teqg_teqo (S):
      ∀T1,T2. T1 ≛[S] T2 → T1 ~ T2.
#S #T1 #T2 * -T1 -T2 /2 width=1 by teqo_sort, teqo_pair/
qed.
