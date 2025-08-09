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
include "delayed_updating/syntax/prototerm_clear_eq.ma".
include "delayed_updating/syntax/prototerm_irefs_or.ma".
include "delayed_updating/syntax/prototerm_irefs_clear.ma".
include "delayed_updating/syntax/prototerm_beta.ma".
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
#t1 #t2 #r #H0t1 * #p #b #q #n * #Hr #_ #_ #H1t1 #_ -t2
* #p0 #q0 #n0 >(path_clear_d_dx … n0) #H0 #Hq0 #H2t1 destruct
lapply (term_clear_inj … H0t1 … H0) -H0
[1,2: /2 width=2 by term_in_root/ ] #H0 destruct
>H0 in H2t1; -p0 -n0 #H2t1
lapply (term_complete_append … H0t1 H1t1 H2t1) -t1 -p -b -q -n #H0 destruct
/2 width=1 by ppc_inv_empty/
qed-.

(* Destructions with pirc ***************************************************)

lemma dbfs_des_in_pirc_dx (t1) (t2) (r):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 → r ϵ 𝐈❨t2❩.
#t1 #t2 #r #H0t1 * #p #b #q #n * #Hr #_ #_ #Ht1 #Ht2 destruct
elim (term_ol_grafted_S_dx_proper … p H0t1)
[2: /2 width=4 by path_beta_pA_in_root/ ] #x #H1x #H2x
@(subset_in_eq_repl_fwd ????? (subset_eq_pirc_bi … Ht2)) -t2
@(subset_le_pirc_bi … (fsubst_le_true …))
[ /2 width=3 by subset_ol_i/ | >(path_clear_beta_b … (⁤↑n) (⁤↑(♭b+n))) ]
/3 width=4 by path_in_pirc, pt_append_in/
qed-.

lemma dbfs_des_le_pirc_bi (t1) (t2) (r):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 → 𝐈❨t1❩ ⊆ 𝐈❨t2❩.
#t1 #t2 #r0 #H0t1 * #p #b #q #n * #Hr0 #_ #_ #Ht1 #Ht2 #r #Hr destruct
lapply (subset_le_pirc_bi ?? (subset_le_or_dx_and_nimp_refl_sn_bi ?? (𝐅❨p,b,q,n❩) …) … Hr) -Hr
[ /2 width=1 by term_in_slice_dec/ | #Hr ]
@(subset_in_eq_repl_fwd ????? (subset_eq_pirc_bi … Ht2)) -t2
@(subset_le_pirc_bi … (fsubst_le_dx …)) [ /2 width=3 by subset_ol_i/ ]
@subset_le_or_pirc
elim (subset_le_pirc_or … Hr) -Hr #Hr
[ lapply (subset_le_pirc_bi ?? (term_le_and_sn_single_dx … H0t1 Ht1 …) … Hr) -Hr #Hr
  lapply (term_le_pirc_bi_clear_dx … Hr) -Hr #Hr
  lapply (subset_in_eq_repl_back ??? Hr ? (subset_eq_pirc_bi …)) [| @clear_single ] -Hr
  >(path_clear_beta_b … (⁤↑n) (⁤↑(♭b+n))) #Hr
  @subset_or_in_sn
  @term_le_pirc_bi_clear_sn
  @(subset_in_eq_repl_fwd ????? (subset_eq_pirc_bi …)) [2: @clear_pt_append || skip ]
  @pirc_le_single_append // -r
  @(subsets_inh_le_repl_fwd … (term_le_clear_grafted_S_dx_dx … H0t1 …))
  /4 width=4 by preterm_clear, term_grafted_S_dx_inh, in_comp_term_clear, path_beta_pA_in_root/
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
