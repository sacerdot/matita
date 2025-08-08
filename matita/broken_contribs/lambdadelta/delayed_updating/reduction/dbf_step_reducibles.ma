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

include "delayed_updating/reduction/prototerm_reducibles.ma".
include "delayed_updating/reduction/dbf_step_preterm_inv.ma".

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)

(* Constructions with prc ***************************************************)

lemma dbfs_prc (t1) (r):
      r ϵ 𝐑❨t1❩ → ∃t2. t1 ➡𝐝𝐛𝐟[r] t2.
#t1 #r * #p #b #q #n #Hr
/2 width=5 by xprc_dbfs/
qed-.

(* Inversions with prc ******************************************************)

lemma dbfs_inv_prc (t1) (t2) (r):
      t1 ➡𝐝𝐛𝐟[r] t2 → r ϵ 𝐑❨t1❩.
#t1 #t2 #r * #p #b #q #n #Hr #_
/2 width=5 by prc_mk/
qed-.

(* Destructions with prc ****************************************************)

lemma dbfs_des_prc_neq (t1) (t2) (r) (s):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 →
      s ⧸= r → s ϵ 𝐑❨t1❩ → s ϵ 𝐑❨t2❩.
#t1 #t2 #r #s #Ht1 #Ht #Hr * #p #b #q #n #Hs
/3 width=10 by prc_mk, dbfs_des_xprc_neq/
qed-.

(* UPDATE *)

lemma dbfs_des_prc_side (t1) (t2) (r) (x) (p) (b) (q) (n):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 → r ϵ 𝐑❨t1,p,b,q,n❩ →
      (⓪p◖𝗦●x) ϵ 𝐑❨t1❩ → r●x ϵ 𝐑❨t2❩.
#t1 #t2 #r #x0 #p #b #q #n #Ht1 #Ht12 #Hr * #p0 #b0 #q0 #n0 #Hx0
elim (term_in_comp_clear_root_slice_dec_xprc … (p◖𝗦) … Hx0) #H0
[ lapply (term_in_clear_root_slice_inv_append_dx_refl … H0) -H0 #H0
  elim (xprc_des_clear_slice … Hx0 H0) -H0
  [ #x #Hx #H0 | /2 width=5 by xprc_des_side/ | // ]
  lapply (eq_inv_list_append_dx_bi … H0) -H0 #H0 destruct
  elim (dbfs_inv_prc_side … Ht1 Ht12 Hr Hx Hx0) -Ht1 -Ht12 -Hr -Hx -Hx0
  * #y #_ #_ #H3 /2 width=5 by prc_mk/
| lapply (xprc_des_r … Hx0) -Hx0 #Hr -b -q -n
  elim (eq_inv_path_append_clear … (sym_eq … Hr)) -Hr #z #x #_ #Hx #_ destruct
  elim H0 -H0 -t1 -t2 -p0 -b0 -q0 -n0 -z
  /3 width=1 by in_comp_term_clear, term_in_comp_root/
]
qed-.

lemma dbfs_des_reduct (t1) (t2) (r) (s):
      t1 ➡𝐝𝐛𝐟[r] t2 → s ϵ 𝐑❨t2❩ →
      ∨∨ s ϵ 𝐑❨t1❩ | r ⊑ s.
#t1 #t2 #r #s
* #p #b #q #n * #Hr #_ #_ #_ #Ht2
* #p0 #b0 #q0 #n0 * #Hs #Hb0 #Hq0 #Hn0 destruct
elim (subset_in_eq_repl_back ??? Hn0 ? Ht2) -t2 * #H1 #H2
[ elim (term_in_append_inv_gen … H2) -H2 #x #Hx #H0 <H0 -p0 -b0 -q0 -n0
  >(path_clear_beta_b … (⁤↑n) (⁤↑(♭b+n)))
  /3 width=2 by path_le_mk, or_intror/
| /3 width=3 by prc_mk_old, or_introl/
]
qed-.

(*
lemma dbfs_inv_prc_eq (t1) (t2) (r):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 →
      r ⧸ϵ 𝐑❨t2❩.
#t1 #t2 #r #Ht1
* #p #b #q #n * #H0 #_ #_ #Hn #Ht2 destruct
* #p0 #b0 #q0 #n0 * #H0 #_ #_ #Hn0
lapply (subset_in_eq_repl_back ??? Hn0 ? Ht2) -t2 #Hn0
lapply (in_comp_term_clear_d_dx … Hn) -Hn #Hn
lapply (in_comp_term_clear_d_dx … Hn0) >H0 -p0 -b0 -q0 -n0 #Hn0
*)
