
include "delayed_updating/substitution/fsubst_fsubst.ma".
include "delayed_updating/reduction/preterm_xfocus_reducible.ma".
include "delayed_updating/reduction/preterm_delayed_xfocus_reducible.ma".
include "delayed_updating/reduction/dbf_step_preterm.ma".
include "delayed_updating/reduction/dbf_devel_preterm.ma".
(*
lemma pippo0 (t) (q1) (q2):
      t ϵ 𝐓 → q1 ϵ ▵t → ⓪q1 = ⓪q2 → q2 ϵ ▵t.
#t #q1 #q2 #Ht #Hq1 #Hq
lapply (in_comp_term_clear … Hq1) >Hq -q1 #Hq2
*)

(* t ϵ 𝐓 → *)

lemma pippo1 (t) (r) (s) (p) (b) (q) (n):
      r ϵ 𝐑❨t,p,b,q,n❩ →
      s ϵ ▵𝐅❨p,b,q❩ → r ϵ ↑(⓪s).
#t #r #s #p #b #q #n #Hr * #x #H0
lapply (xprc_des_r … Hr) -Hr #Hr destruct
lapply (term_grafted_inv_gen … H0) -H0 #H0
elim (in_comp_brxf_inv_gen … H0) -H0 #y #H0
lapply (eq_f ?? path_clear … H0) -H0 #H0

lemma pippo2 (t) (r) (s) (p) (b) (q) (n):
      r ϵ 𝐑❨t,p,b,q,n❩ →
      r ⧸ϵ ↑(⓪s◖𝗦) → s◖𝗦 ⧸ϵ ▵𝐅❨p,b,q❩.
/3 width=7 by pippo1/
qed-.

(* UPDATE *)

lemma dbf_step_conf_local (t0) (t1) (t2) (r1) (r2):
      t0 ϵ 𝐓 → t0 ➡𝐝𝐛𝐟[r1] t1 → t0 ➡𝐝𝐛𝐟[r2] t2 →
      ∃∃t. t1 ⫽➡𝐝𝐛𝐟[r2 /𝐝𝐛𝐟{t0} r1] t & t2 ⫽➡𝐝𝐛𝐟[r1 /𝐝𝐛𝐟{t0} r2] t.
#t0 #t1 #t2 #r1 #r2 #Ht0 #Ht01 #Ht02
elim (eq_path_dec r2 r1) #Hnr12 destruct
[ lapply (dbfs_preterm_mono … Ht0 Ht01 Ht02) -Ht0 -Ht01 -Ht02 #Ht12
  /3 width=3 by dbfd_self, ex2_intro/
| lapply (dbfs_preterm_trans … Ht0 Ht01) #Ht1
  lapply (dbfs_preterm_trans … Ht0 Ht02) #Ht2
  cases Ht01 #p1 #b1 #q1 #n1 #Hr01
  cases Ht02 #p2 #b2 #q2 #n2 #Hr02
  lapply (dbfs_des_xprc_neq … Ht0 Ht01 Hnr12 Hr02) -Ht01
  lapply (dbfs_des_xprc_neq … Ht0 Ht02 … Hr01) -Ht02 [ /2 width=1 by/ ]
  #Hr21 #Hr12 #Ht02 #Ht01
  elim (term_in_slice_dec (⓪p2◖𝗦) r1) #Hp12
  elim (term_in_slice_dec (⓪p1◖𝗦) r2) #Hp21
  [
  |
  |
  | elim (xprc_dbfs … Hr21) #t4 #Ht24
    elim (xprc_dbfs … Hr12) #t3 #Ht13
    cut (t3 ⇔ t4)
    [ lapply (dbfs_preterm_inv_sn … Ht1 Ht13 Hr12) -Ht13 -Hr12 #Ht13
      lapply (dbfs_preterm_inv_sn … Ht2 Ht24 Hr21) -Ht24 -Hr21 #Ht24
      @(fsubst_fsubst_nol_inv_eq ?????????????????????? Ht01 Ht02 Ht13 Ht24)
      [ /2 width=3 by brxf_ol_sn/
      | /2 width=3 by brxf_ol_sn/
      | /3 width=16 by neq_inv_xprc_bi_brxf/
      | /3 width=17 by neq_inv_xprc_bi_brxf_brd/
      | /4 width=17 by neq_inv_xprc_bi_brxf_brd, sym_eq/
      | //
      | //
      | @(brd_grafted_fsubst_eq_repl_fwd … Ht01)
        [ @(pippo2 … Hr01 Hp12) 
      | @(brd_grafted_fsubst_eq_repl_fwd … Ht02)
      ]
    | #Ht34 -Hr21 -Hr12
      @(ex2_intro … t4)
      [ @(dbfd_eq_trans … Ht34)
        @(dbfs_neq_dbfd … Ht0 Hr01 Hnr12 Hp21 Ht13)
      | @(dbfs_neq_dbfd … Ht0 Hr02 … Hp12 Ht24) /2 width=1 by/
      ]
    ]
  ]
]
