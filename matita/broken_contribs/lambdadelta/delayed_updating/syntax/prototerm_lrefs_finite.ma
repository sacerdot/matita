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

include "ground/subsets/subsets_finite_or.ma".
include "delayed_updating/syntax/prototerm_lrefs.ma".

(* SUBSET OF LOCAL REFERENCES ***********************************************)

(* constructions with finite_subsets ****************************************)

lemma subset_le_plrc_single_empty_sn:
      (𝐋❨❴𝐞❵❩) ⊆ Ⓕ.
#r * #s1 #s2 #k #H0 #Hs destruct
lapply (subset_in_inv_single ??? Hs) -Hs #H0
elim (eq_inv_list_append_empty … H0) -H0 #_ #H0 destruct
qed.

lemma subset_le_plrc_single_rcons_sn (p) (l):
      (𝐋❨❴p◖l❵❩) ⊆ 𝐋❨❴p❵❩ ∪ ❴⓪p❵.
#p #l #r * #s1 #s2 #k #H0 #Hs destruct
lapply (subset_in_inv_single ??? Hs) -Hs #H0
elim (eq_inv_list_lcons_append ????? (sym_eq … H0)) -H0 * [| #s ] #H1 #h2 destruct
[ /2 width=1 by subset_or_in_dx/
| /3 width=3 by in_comp_plrc, subset_or_in_sn/
]
qed.

lemma plrc_single_finite (p):
      (𝐋❨❴p❵❩) ϵ 𝛀.
#p elim p -p [| #l #p #IH ]
[ @(subsets_finite_le_trans … (subset_le_plrc_single_empty_sn …)) //
| @(subsets_finite_le_trans … (subset_le_plrc_single_rcons_sn …))
  /2 width=1 by subsets_finite_or/
]
qed.
