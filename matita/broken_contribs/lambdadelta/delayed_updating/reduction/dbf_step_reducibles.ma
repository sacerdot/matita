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

include "delayed_updating/syntax/path_clear_help.ma".
include "delayed_updating/syntax/path_le.ma".
include "delayed_updating/syntax/prototerm_clear_eq.ma".
include "delayed_updating/syntax/preterm_clear.ma".
include "delayed_updating/reduction/prototerm_reducibles.ma".
include "delayed_updating/reduction/dbf_step.ma".

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)

(* Constructions with prc ***************************************************)

lemma dbfs_reducible (t1) (r):
      r ϵ 𝐑❨t1❩ → ∃t2. t1 ➡𝐝𝐛𝐟[r] t2.
#t1 #r * #p #b #q #n #Hr #Hb #Hq #Ht1
/3 width=10 by ex5_4_intro, ex_intro/
qed-.

(* Inversions with prc ******************************************************)

lemma dbfs_inv_reducuble (t1) (t2) (r):
      t1 ➡𝐝𝐛𝐟[r] t2 → r ϵ 𝐑❨t1❩.
#t1 #t2 #r * #p #b #q #n #Hr #Hb #Hq #Ht1 #_ destruct
/2 width=3 by prc_mk/
qed-.

(* Destructions with prc ****************************************************)

lemma dbfs_des_reducuble_neq (t1) (t2) (r) (s):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 →
      s ⧸= r → s ϵ 𝐑❨t1❩ → s ϵ 𝐑❨t2❩.
#t1 #t2 #r #s #Ht1 #Ht #Hr * #p #b #q #n #H0 #Hb #Hq #Hn destruct
elim (dbfs_inv_reducuble … Ht) #p0 #b0 #q0 #n0 #H0 #_ #_ #Hn0 destruct
@(prc_mk … Hq) [| // ] -Hb -Hq
@(dbfs_des_in_comp_neq … Ht) // -t2 #H0
lapply (term_slice_des_clear_bi … (𝐞) … Ht1 … H0) -H0
[ /2 width=2 by term_in_root_rcons/
| /2 width=1 by term_in_comp_root/
]
* #s #_ #Hs >Hs in Hn; #Hn
lapply (term_comp_append … Ht1 Hn0 Hn) -t1 #H0 destruct
<(list_append_lcons_sn) in Hs; <list_append_empty_sn #H0
elim (eq_inv_list_lcons_bi ????? H0) -H0 #_ #Hs -n -n0
/2 width=1 by/
qed-.

lemma dbfs_des_reduct (t1) (t2) (r) (s):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 → s ϵ 𝐑❨t2❩ →
      ∨∨ s ϵ 𝐑❨t1❩ | r ⊑ s.
#t1 #t2 #r #s #Ht1
* #p #b #q #n #Hr #_ #_ #_ #Ht2
* #p0 #b0 #q0 #n0 #Hs #Hb0 #Hq0 #Hn0 destruct
elim (subset_in_eq_repl_back ??? Hn0 ? Ht2) -t2 * #H1 #H2
[ lapply (subset_in_eq_repl_fwd ??? H2 … (pt_append_assoc …)) -H2 #H2
  lapply (in_comp_term_clear_d_dx … H2) -Hb0 -Hq0 -H2 -H1 #H2
  lapply (subset_in_eq_repl_back ??? H2 … (clear_pt_append …)) -H2
  <path_clear_append in ⊢ (%→?); <path_clear_d_dx <path_clear_reduct
  <path_clear_empty <list_append_lcons_sn <list_append_empty_sn #H2
  lapply (term_in_comp_pt_append_des_slice … H2) -H2 #H2
  lapply (term_slice_des_rcons_bi … H2) -H2 #H2
  /2 width=1 by or_intror/
| /3 width=3 by prc_mk, or_introl/
]
qed-.

lemma dbfs_des_reducuble_eq (t1) (t2) (r):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 →
      r ⧸ϵ 𝐑❨t2❩.
#t1 #t2 #r #Ht1
* #p #b #q #n #H0 #_ #_ #Hn #Ht2 destruct
* #p0 #b0 #q0 #n0 #H0 #_ #_ #Hn0
lapply (subset_in_eq_repl_back ??? Hn0 ? Ht2) -t2 #Hn0
lapply (in_comp_term_clear_d_dx … Hn) -Hn #Hn
lapply (in_comp_term_clear_d_dx … Hn0) >H0 -p0 -b0 -q0 -n0 #Hn0
