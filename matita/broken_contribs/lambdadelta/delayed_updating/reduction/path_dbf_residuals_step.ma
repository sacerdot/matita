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

include "delayed_updating/syntax/path_closed_clear.ma".
include "delayed_updating/reduction/prototerm_xfocus_reducible.ma".
include "delayed_updating/reduction/prototerm_reducibles_eq.ma".
include "delayed_updating/reduction/dbf_step_reducibles.ma".
include "delayed_updating/reduction/path_dbf_residuals.ma".

(* RESIDUALS OF A DBF-REDEX POINTER *****************************************)

(* Constructions with dbfs **************************************************)

(* UPDATE *)

lemma path_dbfr_step (t1) (t2) (s) (r):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 →
      s ϵ 𝐑❨t1❩ → s /𝐝𝐛𝐟{t1} r ⊆ 𝐑❨t2❩.
#t1 #t2 #s #r #Ht1 #Ht12 #Hs #x * *
[ #Hnrs #H0 destruct
  /2 width=6 by dbfs_des_reducuble_neq/
| #p #b #q #q0 #n #Hr #H1 #H2 destruct
  lapply (dbfs_preterm_inv_sn … Ht1 Ht12 Hr) -Ht12 #Ht12
  cases Hr #H0 #Hb #Hq #Hn destruct
  lapply (prc_eq_repl … Ht12) -Ht12 #Ht12
  @(subset_in_eq_repl_fwd ????? Ht12) -t2
  cases Hs -Hs #p2 #b2 #q2 #n2 *
  <path_clear_append <path_clear_A_sn <path_clear_append <path_clear_L_sn
  <path_append_pAbLq_1 #H0 #Hb2 #Hq2 #Hn2
  elim (path_eq_inv_pbq_pSq_pbc … H0) -H0 [3: // ] * #m0
  [ >path_clear_A_dx #H0 #H1 destruct -Hb -Hq
    elim (eq_inv_path_append_clear … (sym_eq … H0)) -H0 #r #s #Hr #H1 #H2
    elim (eq_inv_path_S_sn_clear … H1) -H1 #m #H3 #H4 destruct
    <list_append_rcons_sn in H2; #H2
    elim (eq_inv_list_lcons_append ????? (sym_eq … H2)) -H2 *
    [ #_ #H0 | #l #H1 #H2 ] destruct
    >(list_append_rcons_sn ? l r ?) in Hn2; >path_append_pAbLq_8 #Hn2
    lapply (term_clear_inj … Ht1 … Hr) -Ht1 -Hr
    [3: |*: /2 width=2 by term_in_root/ ] #H0 destruct
    >path_clear_reduct >(path_clear_d_dx … (⁤↑(♭b+n))) >path_clear_L_sn
    >path_clear_append >path_clear_append >path_clear_append
    <(path_append_pAbLq_8 ?? b2)
    @(prc_mk_old … Hb2 Hq2) -Hb2 -Hq2
    @fsubst_in_comp_true [ @(brxf_ol_sn … Hr) ] -Hr
    >(list_append_rcons_sn ? l) <list_append_assoc >(path_append_pAbLq_9 ?? b2)
    @pt_append_in <list_append_rcons_dx
    @in_comp_iref_hd @term_grafted_gen //
  | -Hb #H1 >list_append_rcons_sn #H2
    elim (eq_inv_list_rcons_append ????? H1) -H1 *
    [ #H0 #_ elim (eq_inv_list_rcons_bi ????? H0) -H0 #_ #H0 destruct ]
    #l0 #H1 #H0 destruct
    elim (eq_inv_path_append_clear … (sym_eq … H1)) -H1 #l #x #H3 #H1 #H4 destruct
    elim (eq_inv_path_S_sn_clear … H1) -H1 #r #H3 #H4 destruct
    >path_clear_reduct >(path_clear_d_dx … (⁤↑(♭b+n))) >path_clear_append
    >path_clear_L_sn in H2; >path_clear_append >path_clear_A_sn >path_clear_append #H2
    lapply (term_clear_inj … Ht1 … H2) -Ht1 -H2
    [3: |*: /2 width=2 by term_in_root/ ] #H0 destruct
    <path_append_pAbLq_10 in Hn; #Hn
    <brd_unfold <path_append_pAbLq_10 <path_append_pAbLqAbLq_1
    @(prc_mk_old … n2 … Hb2) -Hb2
    [ @fsubst_in_comp_true [ @(brxf_ol_sn … Hr) ] -Hr
      <path_append_pAbLqAbLq_2
      @pt_append_in @in_comp_iref_hd @term_grafted_gen //
    | -t1 -p2 -b2 <path_append_pAbLq_11 >nplus_succ_dx >nplus_unit_sn
      lapply (pcc_inv_S … Hq2) -Hq2 #Hq2
      @pcc_d @pcc_d @(pcc_pcc … Hq) @pcc_L -Hq
      @(pcc_pcc (⓪b) (♭b)) [ // ] @pcc_A //
    ]
  ]
]
qed.
