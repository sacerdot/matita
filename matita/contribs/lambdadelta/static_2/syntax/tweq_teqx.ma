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

include "static_2/syntax/teqx.ma".
include "static_2/syntax/tweq.ma".

(* SORT-IRRELEVANT WHD EQUIVALENCE ON TERMS *********************************)

(* Properties with sort-irrelevant equivalence for terms ********************)

lemma teqx_tweq: ∀T1,T2. T1 ≛ T2 → T1 ≅ T2.
#T1 #T2 #H elim H -T1 -T2 [||| * [ #p ] * #V1 #V2 #T1 #T2 #_ #_ #IHV #IHT ]
[ /1 width=1 by tweq_sort/
| /1 width=1 by tweq_lref/
| /1 width=1 by tweq_gref/
| cases p -p /2 width=1 by tweq_abbr_pos, tweq_abbr_neg/  
| /1 width=1 by tweq_abst/
| /2 width=1 by tweq_appl/
| /2 width=1 by tweq_cast/
]
qed.
