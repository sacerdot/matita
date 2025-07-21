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

include "ground/subsets/subset_nimply_and_or_le.ma".
include "ground/subsets/subset_lt.ma".
include "delayed_updating/syntax/path_clear_help.ma".
include "delayed_updating/syntax/prototerm_constructors_eq.ma".
include "delayed_updating/syntax/prototerm_clear_eq.ma".
include "delayed_updating/syntax/prototerm_irefs_or.ma".
include "delayed_updating/syntax/prototerm_irefs_constructors.ma".
include "delayed_updating/syntax/prototerm_irefs_clear.ma".
include "delayed_updating/syntax/preterm_inhabited.ma".
include "delayed_updating/syntax/preterm_proper.ma".
include "delayed_updating/syntax/preterm_clear_eq.ma".
include "delayed_updating/substitution/fsubst_eq.ma".
include "delayed_updating/reduction/dbf_step.ma".

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)

(* Inversions with pirc *****************************************************)

(* UPDATE *)

lemma dbfs_inv_nin_pirc_sn (t1) (t2) (r):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 → r ⧸ϵ 𝐈❨t1❩.
#t1 #t2 #r #H0t1 * #p #b #q #n * #Hr #_ #_ #H1t1 #_
* #p0 #q0 #n0 #H0 #Hq0 #H2t1 destruct
lapply (term_clear_inj … H0t1 … H0) -H0
[1,2: /2 width=2 by term_in_root/ ] #H0 destruct
lapply (term_root_d_post … H0t1 (p●𝗔◗b●𝗟◗q) (𝗱n0) (⁤↑n) ??)
[1,2: /2 width=2 by term_in_root/ ] #H0 destruct
lapply (term_complete_post … H0t1 … H2t1 H1t1 ?) -t1 // #H0
lapply (eq_inv_list_append_dx_dx_refl … (sym_eq … H0)) -H0 #H0 destruct
/2 width=1 by ppc_inv_empty/
qed-.

(* Destructions with pirc ***************************************************)

lemma dbfs_des_in_pirc_dx (t1) (t2) (r):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 → r ϵ 𝐈❨t2❩.
#t1 #t2 #r #H0t1 * #p #b #q #n * #Hr #_ #_ #Ht1 #Ht2 destruct
@(subset_in_eq_repl_fwd ????? (subset_eq_pirc_bi … Ht2)) -t2
@(subset_le_pirc_bi … (fsubst_le_true …))
[ /2 width=3 by subset_ol_i/ | >path_clear_reduct ]
/4 width=2 by pirc_mk_iref, term_ol_grafted_S_dx_proper, term_in_root/
qed-.

lemma dbfs_des_le_pirc_bi (t1) (t2) (r):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 → 𝐈❨t1❩ ⊆ 𝐈❨t2❩.
#t1 #t2 #r0 #H0t1 * #p #b #q #n * #Hr0 #_ #_ #Ht1 #Ht2 #r #Hr destruct
lapply (subset_le_pirc_bi ?? (subset_le_or_dx_and_nimp_refl_sn_bi ?? (↑(p●𝗔◗b●𝗟◗q)) …) … Hr) -Hr
[ /2 width=1 by term_in_slice_dec/ | #Hr ]
@(subset_in_eq_repl_fwd ????? (subset_eq_pirc_bi … Ht2)) -t2
@(subset_le_pirc_bi … (fsubst_le_dx …)) [ /2 width=3 by subset_ol_i/ ]
@subset_le_or_pirc
elim (subset_le_pirc_or … Hr) -Hr #Hr
[ lapply (subset_le_pirc_bi ?? (term_le_and_sn_single_dx … H0t1 Ht1 …) … Hr) -Hr #Hr
  lapply (term_le_pirc_bi_clear_dx … Hr) -Hr #Hr
  lapply (subset_in_eq_repl_back ??? Hr ? (subset_eq_pirc_bi …)) [| @clear_single ] -Hr
  <path_clear_d_dx >path_clear_reduct #Hr
  @subset_or_in_sn
  @(subset_le_pirc_bi ?? (term_le_pt_append_bi_iref_dx …))
  @term_le_pirc_bi_clear_sn
  @(subset_in_eq_repl_fwd ????? (subset_eq_pirc_bi …)) [2: @clear_pt_append || skip ]
  @pirc_le_single_append // -r
  @(subsets_inh_le_repl_fwd … (term_le_clear_grafted_S_dx_dx … H0t1 …))
  /4 width=2 by preterm_clear, term_grafted_S_dx_inh, in_comp_term_clear, term_in_root/
| /2 width=1 by subset_or_in_dx/
]
qed-.

lemma dbfs_des_in_comp_nimp_pirc_bi (t1) (t2) (r):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 → r ϵ 𝐈❨t2❩ ⧵ 𝐈❨t1❩.
/3 width=6 by dbfs_des_in_pirc_dx, dbfs_inv_nin_pirc_sn, subset_in_nimp/
qed-.

lemma dbfs_des_lt_pirc_bi (t1) (t2) (r):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 → 𝐈❨t1❩ ⊂ 𝐈❨t2❩.
/4 width=5 by dbfs_des_le_pirc_bi, subset_lt_mk, subsets_inh_in, dbfs_des_in_comp_nimp_pirc_bi/
qed-.
