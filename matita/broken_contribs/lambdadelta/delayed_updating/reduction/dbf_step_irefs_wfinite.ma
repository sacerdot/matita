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

include "ground/subsets/subset_nimply_le.ma".
include "delayed_updating/syntax/prototerm_wfinite.ma".
include "delayed_updating/syntax/prototerm_clear_or.ma".
include "delayed_updating/syntax/prototerm_clear_wfinite.ma".
include "delayed_updating/syntax/prototerm_irefs_or.ma".
include "delayed_updating/syntax/prototerm_irefs_lrefs.ma".
include "delayed_updating/syntax/prototerm_lrefs_wfinite.ma".
include "delayed_updating/substitution/fsubst_eq.ma".
include "delayed_updating/reduction/dbf_step.ma".

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)

(* Inversions with pir and subsets_wfinite **********************************)

lemma dbfs_clear_pir_wfinite_sx (t1) (t2) (r):
      t1 ➡𝐝𝐛𝐟[r] t2 → ⓪𝐈❨t1❩ ϵ 𝐖𝛀 → ⓪𝐈❨t2❩ ϵ 𝐖𝛀.
#t1 #t2 #r * #p #b #q #n #Hr #Ht12 #Ht1
lapply (pcxr_des_n … Hr) -Hr #Hn
lapply (subset_eq_trans … (fsubst_eq …) … Ht12) -Ht12
[ /2 width=3 by subset_ol_i/ ] -Hn #Ht12
lapply (subset_eq_pir_bi … Ht12) -Ht12 * #_ #Ht21
lapply (clear_le_repl … Ht21) -Ht21 #Ht21
@(subsets_wfinite_le_trans … Ht21) -t2
@(subsets_wfinite_le_trans … (clear_le_repl … (pir_or_le …)))
@(subsets_wfinite_le_trans … (clear_or_le …))
@subsets_wfinite_or
[ @(subsets_wfinite_le_trans … (clear_le_repl … (pir_pt_append_sx …)))
  @(subsets_wfinite_le_trans … (clear_or_le …))
  @subsets_wfinite_or [ /2 width=1 by term_clear_wfinite/ ]
  @(subsets_wfinite_le_trans … (clear_pt_append_le …))
  @term_pt_append_wfinite
  @(subsets_wfinite_le_trans … (clear_le_repl … (term_le_pir_grafted_sx …)))
  @(subsets_wfinite_le_trans … (term_clear_grafted_le …))
  /2 width=1 by term_grafted_wfinite/
| @(subsets_wfinite_le_trans … Ht1) -Ht1
  @clear_le_repl
  @subset_le_pir_bi //
]
qed-.
