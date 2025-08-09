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

include "ground/subsets/subsets_wfinite_or.ma".
include "delayed_updating/syntax/prototerm_lrefs.ma".

(* SUBSET OF LOCAL REFERENCES ***********************************************)

(* constructions with subsets_wfinite ***************************************)

lemma subset_le_plrc_single_empty_sn:
      (𝐋❨❴𝐞❵❩) ⊆ Ⓕ.
#r * #s1 #s2 #k #H0 #Hs destruct
lapply (subset_in_inv_single ??? Hs) -Hs #H0
elim (eq_inv_list_append_empty … H0) -H0 #_ #H0 destruct
qed.

lemma subset_le_plrc_single_rcons_sn (p) (l):
      (𝐋❨❴p◖l❵❩) ⊆ 𝐋❨❴p❵❩ ∪ ❴(⓪p)◖𝗱𝟎❵.
#p #l #r * #s1 #s2 #k #H0 #Hs destruct
lapply (subset_in_inv_single ??? Hs) -Hs #H0
elim (eq_inv_list_lcons_append ????? (sym_eq … H0)) -H0 * [| #s ] #H1 #H2 destruct
[ /2 width=1 by subset_or_in_dx/
| /3 width=3 by path_in_plrc, subset_or_in_sn/
]
qed.

lemma plrc_single_wfinite (p):
      (𝐋❨❴p❵❩) ϵ 𝐖𝛀.
#p elim p -p [| #l #p #IH ]
[ @(subsets_wfinite_le_trans … (subset_le_plrc_single_empty_sn …)) //
| @(subsets_wfinite_le_trans … (subset_le_plrc_single_rcons_sn …))
  /2 width=1 by subsets_wfinite_or/
]
qed.
