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
include "ground/subsets/subset_or.ma".
include "ground/subsets/subset_listed_1.ma".
include "delayed_updating/syntax/prototerm.ma".
include "delayed_updating/syntax/prototerm_lrefs.ma".
include "delayed_updating/syntax/prototerm_irefs.ma".

(* SUBSET OF INNER REFERENCES ***********************************************)

(* constructions with plrc **************************************************)

lemma pir_pt_append_sx (t) (p):
      (𝐈❨p●t❩) ⊆ 𝐋❨❴p❵❩ ∪ (p●𝐈❨t❩).
#t #p #r * #r1 #r2 #k #Hr1 #Hr2 * #q #Hq #H0 destruct
elim (eq_inv_list_append_bi … H0) -H0 * #s2 #H1 #H2 destruct
[ /3 width=3 by plr_mk, subset_or_in_sx/
| elim (eq_inv_list_lcons_append ????? H1) -H1 * [| #s1 ] #H1 #H2 destruct
  [ /3 width=3 by plr_mk, subset_or_in_sx/
  | /4 width=4 by pir_mk, pt_append_in, subset_or_in_dx/
  ]
]
qed.
