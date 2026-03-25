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

lemma subset_le_plr_single_empty_sx:
      (𝐋❨❴𝐞❵❩) ⊆ Ⓕ.
#r * #s1 #s2 #k #H0 #Hs destruct
lapply (subset_in_inv_single ??? Hs) -Hs #H0
elim (eq_inv_list_append_empty … H0) -H0 #_ #H0 destruct
qed.

lemma subset_le_plr_single_rcons_sx (p) (l):
      (𝐋❨❴p◖l❵❩) ⊆ 𝐋❨❴p❵❩ ∪ ❴p◖l❵.
#p #l #r * #s1 #s2 #k #H0 #Hs destruct
lapply (subset_in_inv_single ??? Hs) -Hs #H0
elim (eq_inv_list_lcons_append ????? (sym_eq … H0)) -H0 * [| #s ] #H1 #H2 destruct
[ /2 width=1 by subset_or_in_dx/
| /3 width=3 by plr_mk, subset_or_in_sx/
]
qed.

lemma plr_single_wfinite (p):
      (𝐋❨❴p❵❩) ϵ 𝐖𝛀.
#p elim p -p [| #l #p #IH ]
[ @(subsets_wfinite_le_trans … (subset_le_plr_single_empty_sx …)) //
| @(subsets_wfinite_le_trans … (subset_le_plr_single_rcons_sx …))
  /2 width=1 by subsets_wfinite_or/
]
qed.
