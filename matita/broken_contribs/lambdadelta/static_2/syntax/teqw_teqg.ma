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
include "static_2/syntax/teqw.ma".

(* SORT-IRRELEVANT WHD EQUIVALENCE ON TERMS *********************************)

(* Properties with generic equivalence for terms ****************************)

lemma teqg_teqw (S):
      ∀T1,T2. T1 ≛[S] T2 → T1 ≃ T2.
#S #T1 #T2 #H elim H -T1 -T2 [||| * [ #p ] * #V1 #V2 #T1 #T2 #_ #_ #IHV #IHT ]
[ /1 width=1 by teqw_sort/
| /1 width=1 by teqw_lref/
| /1 width=1 by teqw_gref/
| cases p -p /2 width=1 by teqw_abbr_pos, teqw_abbr_neg/
| /1 width=1 by teqw_abst/
| /2 width=1 by teqw_appl/
| /2 width=1 by teqw_cast/
]
qed.
