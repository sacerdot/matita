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
include "delayed_updating/syntax/prototerm_constructors_eq.ma".
include "delayed_updating/syntax/prototerm_irefs_or.ma".
include "delayed_updating/syntax/prototerm_irefs_lrefs.ma".
include "delayed_updating/syntax/prototerm_lrefs_wfinite.ma".
include "delayed_updating/substitution/fsubst_eq.ma".
include "delayed_updating/reduction/dbf_step.ma".

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)

(* Inversions with pirc and subsets_wfinite *********************************)

(* UPDATE *)

lemma dbfs_pirc_wfinite_sn (t1) (t2) (r):
      t1 ➡𝐝𝐛𝐟[r] t2 → 𝐈❨t1❩ ϵ 𝐖𝛀 → 𝐈❨t2❩ ϵ 𝐖𝛀.
#t1 #t2 #r * #p #b #q #n * #H0 #_ #_ #Hn * #_ #Ht21 #H2t1 destruct
lapply (subset_le_trans … Ht21 … (fsubst_le_sn …)) -Ht21
[ /2 width=3 by subset_ol_i/ ] -Hn #Ht21
lapply (subset_le_pirc_bi … Ht21) -Ht21 #Ht21
@(subsets_wfinite_le_trans … Ht21) -t2
@(subsets_wfinite_le_trans … (subset_le_pirc_or …))
@subsets_wfinite_or
[ @subsets_wfinite_le_trans
  [| @(subset_le_pirc_bi … (term_le_pt_append_bi_iref_sn …)) ]
  @(subsets_wfinite_le_trans … (pirc_pt_append_sn …))
  @subsets_wfinite_or //
  @term_pt_append_wfinite
  @(subsets_wfinite_le_trans … (term_le_pirc_grafted_sn …))
  /2 width=1 by term_grafted_wfinite/
| @(subsets_wfinite_le_trans … H2t1) -H2t1
  @subset_le_pirc_bi //
]
qed-.
