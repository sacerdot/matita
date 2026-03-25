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

include "ground/subsets/subset_lt.ma".
include "ground/subsets/subset_nimply_and_or_le.ma".
include "delayed_updating/syntax/path_beta_clear.ma".
include "delayed_updating/syntax/prototerm_clear_eq.ma".
include "delayed_updating/syntax/prototerm_clear_or.ma".
include "delayed_updating/syntax/prototerm_clear_single.ma".
include "delayed_updating/syntax/prototerm_irefs_or.ma".
include "delayed_updating/syntax/prototerm_irefs_clear.ma".
include "delayed_updating/syntax/prototerm_beta.ma".
include "delayed_updating/syntax/preterm_inhabited.ma".
include "delayed_updating/syntax/preterm_proper.ma".
include "delayed_updating/syntax/preterm_clear_eq.ma".
include "delayed_updating/substitution/fsubst_eq.ma".
include "delayed_updating/reduction/dbf_step.ma".

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)

(* Inversions with pir ******************************************************)

(* UPDATE *)

lemma dbfs_inv_nin_clear_pir_sx (t1) (t2) (r):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 → ⓪r ⧸ϵ ⓪𝐈❨t1❩.
#t1 #t2 #r #Ht1 * #p #b #q #n #Hr #_ -t2
lapply (pcxr_des_eq … Hr) #H0
lapply (pcxr_des_n … Hr) #Hn -Hr destruct
* #x * #p0 #q0 #n0 #H1 #Hq0 #Hn0 #H2 destruct
lapply (term_clear_inj … Ht1 … H2) -H2
[1,2: /2 width=2 by term_in_root/ ] #H2
<H2 in Hn0; -p0 -n0 #Hq0
lapply (term_complete_append … Ht1 Hn Hq0) -t1 -p -b -q -n #H0 destruct
/2 width=1 by ppc_inv_empty/
qed-.

(* Destructions with pir ****************************************************)

lemma dbfs_des_in_clear_pir_dx (t1) (t2) (r):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 → ⓪r ϵ ⓪𝐈❨t2❩.
#t1 #t2 #r #Ht1 * #p #b #q #n #Hr #Ht2
lapply (pcxr_des_eq … Hr) #H0
lapply (pcxr_des_n … Hr) #Hn -Hr destruct
elim (term_ol_grafted_S_dx_proper … p Ht1)
[2: /2 width=4 by path_beta_pA_in_root/ ] #x #H1x #H2x
lapply (subset_le_eq_repl … (subset_eq_refl …) … Ht2) -Ht2
[ @(fsubst_le_true …) /2 width=3 by subset_ol_i/ | skip ] #Ht2
>(path_clear_beta_b … (⁤↑n) (⁤↑(♭b+n)))
@(clear_le_repl … (subset_le_pir_bi … Ht2)) -t2
/4 width=4 by pir_mk, in_comp_term_clear, pt_append_in/
qed-.

lemma dbfs_des_le_clear_pir_bi (t1) (t2) (r):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 → ⓪𝐈❨t1❩ ⊆ ⓪𝐈❨t2❩.
#t1 #t2 #r #Ht1 * #p #b #q #n #Hr #Ht2
lapply (pcxr_des_n … Hr) -Hr #Hn #x0 * #x #Hx #H0 destruct
lapply (subset_eq_trans … (fsubst_eq …) … Ht2) -Ht2
[ /2 width=5 by subset_ol_i/ ] #Ht2
lapply (subset_eq_pir_bi … Ht2) -Ht2 #Ht2
lapply (subset_eq_trans … (pir_or …) … Ht2) -Ht2 #Ht2
lapply (clear_eq_repl … Ht2) -Ht2 #Ht2
lapply (subset_eq_trans … (clear_or_eq …) … Ht2) -Ht2 #Ht2
@(subset_in_eq_repl_fwd ????? Ht2) -t2
lapply (subset_le_pir_bi ?? (subset_le_or_dx_and_nimp_refl_sx_bi ?? (𝐅❨p,b,q,n❩) …) … Hx) -Hx
[ /2 width=1 by term_in_slice_dec/ ] #Hx
elim (pir_or_le … Hx) -Hx #Hx
[ lapply (subset_le_pir_bi ?? (term_le_and_sx_single_dx … Ht1 Hn …) … Hx) -Hx #Hx
  lapply (in_comp_term_clear … Hx) -Hx #Hx
  lapply (pir_clear_ge … Hx) -Hx #Hx
  lapply (subset_le_pir_bi … (term_clear_single_le …) … Hx) -Hx
  >(path_clear_beta_b … (⁤↑n) (⁤↑(♭b+n))) #Hx
  @subset_or_in_sx
  @pir_clear_le
  @(subset_in_eq_repl_fwd ????? (subset_eq_pir_bi …))
  [2: @clear_pt_append |3: skip ]
  @pir_le_single_append // -x
  @(subsets_inh_le_repl_fwd … (term_le_clear_grafted_S_dx_dx … Ht1 …))
  /4 width=4 by preterm_clear, term_grafted_S_dx_inh, in_comp_term_clear, path_beta_pA_in_root/
| /3 width=1 by in_comp_term_clear, subset_or_in_dx/
]
qed-.

lemma dbfs_des_in_comp_nimp_clear_pir_bi (t1) (t2) (r):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 → ⓪r ϵ ⓪𝐈❨t2❩ ⧵ ⓪𝐈❨t1❩.
/3 width=6 by dbfs_des_in_clear_pir_dx, dbfs_inv_nin_clear_pir_sx, subset_in_nimp/
qed-.

lemma dbfs_des_lt_clear_pir_bi (t1) (t2) (r):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 → ⓪𝐈❨t1❩ ⊂ ⓪𝐈❨t2❩.
/4 width=5 by dbfs_des_le_clear_pir_bi, subset_lt_mk, subsets_inh_in, dbfs_des_in_comp_nimp_clear_pir_bi/
qed-.
