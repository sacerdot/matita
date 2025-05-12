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
include "delayed_updating/syntax/path_closed_clear.ma".
include "delayed_updating/reduction/prototerm_reducibles_eq.ma".
include "delayed_updating/reduction/prototerm_xfocus_reducible.ma".
include "delayed_updating/reduction/dbf_step_preterm.ma".

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)

(* Constructions with prc ***************************************************)

lemma dbfs_reducible (t1) (r):
      r ϵ 𝐑❨t1❩ → ∃t2. t1 ➡𝐝𝐛𝐟[r] t2.
#t1 #r * #p #b #q #n #Hr
/2 width=5 by xprc_dbfs/
qed-.

(* Inversions with prc ******************************************************)

lemma dbfs_inv_reducuble (t1) (t2) (r):
      t1 ➡𝐝𝐛𝐟[r] t2 → r ϵ 𝐑❨t1❩.
#t1 #t2 #r * #p #b #q #n #Hr #_
/2 width=5 by prc_mk/
qed-.

(* Destructions with prc ****************************************************)

lemma dbfs_des_reducuble_neq (t1) (t2) (r) (s):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 →
      s ⧸= r → s ϵ 𝐑❨t1❩ → s ϵ 𝐑❨t2❩.
#t1 #t2 #r #s #Ht1 #Ht #Hr * #p #b #q #n #Hs
/3 width=10 by prc_mk, dbfs_des_xprc_neq/
qed-.

(* UPDATE *)

lemma dbfs_des_reducible_side (t1) (t2) (r) (x) (p) (b) (q) (n):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 → r ϵ 𝐑❨t1,p,b,q,n❩ →
      (⓪p●𝗦◗x) ϵ 𝐑❨t1❩ → r◖𝗱𝟎●x ϵ 𝐑❨t2❩.
#t1 #t2 #r #x #p #b #q #n #Ht1 #Ht12 #Hr #Hx
lapply (dbfs_preterm_inv_sn … Ht1 Ht12 Hr) -Ht12 #Ht12
cases Hr #H0 #Hb #Hq #Hn destruct
lapply (prc_eq_repl … Ht12) -Ht12 #Ht12
@(subset_in_eq_repl_fwd ????? Ht12) -t2
cases Hx -Hx #p0 #b0 #q0 #n0 *
<path_clear_append <path_clear_A_sn <path_clear_append <path_clear_L_sn
<path_append_pAbLq_1 #H0 #Hb0 #Hq0 #Hn0
elim (path_eq_inv_pbq_pSq_pbc … H0) -H0 [3: // ] * #m0
[ >path_clear_A_dx #H0 #H1 destruct -Hb -Hq
  elim (eq_inv_path_append_clear … (sym_eq … H0)) -H0 #r #s #Hr #H1 #H2
  elim (eq_inv_path_S_sn_clear … H1) -H1 #m #H3 #H4 destruct
  <list_append_rcons_sn in H2; #H2
  elim (eq_inv_list_lcons_append ????? (sym_eq … H2)) -H2 *
  [ #_ #H0 | #l #H1 #H2 ] destruct
  >(list_append_rcons_sn ? l r ?) in Hn0; >path_append_pAbLq_8 #Hn0
  lapply (term_clear_inj … Ht1 … Hr) -Ht1 -Hr
  [3: |*: /2 width=2 by term_in_root/ ] #H0 destruct
  >path_clear_reduct >(path_clear_d_dx … (⁤↑(♭b+n))) >path_clear_L_sn
  >path_clear_append >path_clear_append >path_clear_append
  <(path_append_pAbLq_8 ?? b0)
  @(prc_mk_old … Hb0 Hq0) -Hb0 -Hq0
  @fsubst_in_comp_true [ @(brxf_ol_sn … Hr) ] -Hr
  >(list_append_rcons_sn ? l) <list_append_assoc >(path_append_pAbLq_9 ?? b0)
  @pt_append_in <list_append_rcons_dx
  @in_comp_iref_hd @term_grafted_gen //
| -Hb #H1 >list_append_rcons_sn #H2
  elim (eq_inv_list_rcons_append ????? H1) -H1 *
  [ #H0 #_ elim (eq_inv_list_rcons_bi ????? H0) -H0 #_ #H0 destruct ]
  #l0 #H1 #H0 destruct
  elim (eq_inv_path_append_clear … (sym_eq … H1)) -H1 #l #y #H3 #H1 #H4 destruct
  elim (eq_inv_path_S_sn_clear … H1) -H1 #r #H3 #H4 destruct
  >path_clear_reduct >(path_clear_d_dx … (⁤↑(♭b+n))) >path_clear_append
  >path_clear_L_sn in H2; >path_clear_append >path_clear_A_sn >path_clear_append #H2
  lapply (term_clear_inj … Ht1 … H2) -Ht1 -H2
  [3: |*: /2 width=2 by term_in_root/ ] #H0 destruct
  <path_append_pAbLq_10 in Hn; #Hn
  <brd_unfold <path_append_pAbLq_10 <path_append_pAbLqAbLq_1
  @(prc_mk_old … n0 … Hb0) -Hb0
  [ @fsubst_in_comp_true [ @(brxf_ol_sn … Hr) ] -Hr
    <path_append_pAbLqAbLq_2
    @pt_append_in @in_comp_iref_hd @term_grafted_gen //
  | -t1 -p0 -b0 <path_append_pAbLq_11 >nplus_succ_dx >nplus_unit_sn
    lapply (pcc_inv_S … Hq0) -Hq0 #Hq0
    @pcc_d @pcc_d @(pcc_pcc … Hq) @pcc_L -Hq
    @(pcc_pcc (⓪b) (♭b)) [ // ] @pcc_A //
  ]
]
qed-.

lemma dbfs_des_reduct (t1) (t2) (r) (s):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 → s ϵ 𝐑❨t2❩ →
      ∨∨ s ϵ 𝐑❨t1❩ | r ⊑ s.
#t1 #t2 #r #s #Ht1
* #p #b #q #n * #Hr #_ #_ #_ #Ht2
* #p0 #b0 #q0 #n0 * #Hs #Hb0 #Hq0 #Hn0 destruct
elim (subset_in_eq_repl_back ??? Hn0 ? Ht2) -t2 * #H1 #H2
[ lapply (subset_in_eq_repl_fwd ??? H2 … (pt_append_assoc …)) -H2 #H2
  lapply (in_comp_term_clear_d_dx … H2) -Hb0 -Hq0 -H2 -H1 #H2
  lapply (subset_in_eq_repl_back ??? H2 … (clear_pt_append …)) -H2
  <path_clear_append in ⊢ (%→?); <path_clear_d_dx <path_clear_reduct
  <path_clear_empty <list_append_lcons_sn <list_append_empty_sn #H2
  lapply (term_in_comp_pt_append_des_slice … H2) -H2 #H2
  lapply (term_slice_des_rcons_bi … H2) -H2 #H2
  /2 width=1 by or_intror/
| /3 width=3 by prc_mk_old, or_introl/
]
qed-.

(*
lemma dbfs_inv_reducuble_eq (t1) (t2) (r):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 →
      r ⧸ϵ 𝐑❨t2❩.
#t1 #t2 #r #Ht1
* #p #b #q #n * #H0 #_ #_ #Hn #Ht2 destruct
* #p0 #b0 #q0 #n0 * #H0 #_ #_ #Hn0
lapply (subset_in_eq_repl_back ??? Hn0 ? Ht2) -t2 #Hn0
lapply (in_comp_term_clear_d_dx … Hn) -Hn #Hn
lapply (in_comp_term_clear_d_dx … Hn0) >H0 -p0 -b0 -q0 -n0 #Hn0
*)
