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

include "delayed_updating/syntax/path_beta_clear.ma".
include "delayed_updating/reduction/prototerm_c_redex.ma".
include "delayed_updating/reduction/dbf_step_inv.ma".
include "delayed_updating/reduction/dbf_step_preterm.ma".

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)

(* Constructions with pcr ***************************************************)

lemma dbfs_pcr (t1) (r):
      r ϵ 𝐑❨t1❩ → ∃t2. t1 ➡𝐝𝐛𝐟[r] t2.
#t1 #r * #p #b #q #n #Hr
/2 width=5 by pcxr_dbfs/
qed-.

(* Inversions with pcr ******************************************************)

lemma dbfs_inv_pcr (t1) (t2) (r):
      t1 ➡𝐝𝐛𝐟[r] t2 → r ϵ 𝐑❨t1❩.
#t1 #t2 #r * #p #b #q #n #Hr #_
/2 width=5 by pcr_mk/
qed-.

(* Destructions with pcr ****************************************************)

lemma dbfs_des_pcr_nrle (t1) (t2) (r) (s):
      t1 ➡𝐝𝐛𝐟[r] t2 →
      r ⧸⊑ s → s ϵ 𝐑❨t1❩ → s ϵ 𝐑❨t2❩.
#t1 #t2 #r #s #Ht12 #Hnrs * #p #b #q #n #Hs
/3 width=9 by pcr_mk, dbfs_des_pcxr_nrle/
qed-.

lemma dbfs_des_pcr_neq (t1) (t2) (r) (s):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 →
      s ⧸= r → s ϵ 𝐑❨t1❩ → s ϵ 𝐑❨t2❩.
#t1 #t2 #r #s #Ht1 #Ht12 #Hnrs * #p #b #q #n #Hs
/3 width=10 by pcr_mk, dbfs_des_pcxr_neq/
qed-.

lemma dbfs_des_pcr_side (t1) (t2) (r) (x) (p) (b) (q) (n):
      t1 ➡𝐝𝐛𝐟[r] t2 → r ϵ 𝐑❨t1,p,b,q,n❩ →
      p◖𝗦●x ϵ 𝐑❨t1❩ → 𝐫❨p,⓪b,q,⁤↑(♭b+n)❩●x ϵ 𝐑❨t2❩.
#t1 #t2 #r #x #p #b #q #n #Ht12 #Hr * #p0 #b0 #q0 #n0 #Hx
elim (dbfs_inv_pcxr_side … Ht12 Hr Hx) -t1 -r * #y #H1 #H2 #Hy destruct
/2 width=5 by pcr_mk/
qed-.

lemma dbfs_des_reduct (t1) (t2) (r) (s):
      t1 ➡𝐝𝐛𝐟[r] t2 → s ϵ 𝐑❨t2❩ →
      ∨∨ s ϵ 𝐑❨t1❩ | ⓪r ⊑ ⓪s.
#t1 #t2 #r #s * #p #b #q #n #Hr #Ht12
lapply (pcxr_des_eq … Hr) -Hr #H0 destruct
* #p0 #b0 #q0 #n0 * #H1s #H2s
elim (subset_in_eq_repl_back ??? H1s ? Ht12) -t2 * #H1 #H2
[ elim (term_in_append_inv_gen … H2) -H2 #x #Hx #H0 <H0 -p0 -b0 -q0 -n0
  >(path_clear_beta_b … (⁤↑n) (⁤↑(♭b+n)))
  /3 width=2 by path_rle_mk, or_intror/
| /4 width=5 by pcr_mk, subset_and_in, or_introl/
]
qed-.

(*
lemma dbfs_inv_pcr_eq (t1) (t2) (r):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 →
      r ⧸ϵ 𝐑❨t2❩.
#t1 #t2 #r #Ht1
* #p #b #q #n * #H0 #_ #_ #Hn #Ht2 destruct
* #p0 #b0 #q0 #n0 * #H0 #_ #_ #Hn0
lapply (subset_in_eq_repl_back ??? Hn0 ? Ht2) -t2 #Hn0
lapply (in_comp_term_clear_d_dx … Hn) -Hn #Hn
lapply (in_comp_term_clear_d_dx … Hn0) >H0 -p0 -b0 -q0 -n0 #Hn0
*)
