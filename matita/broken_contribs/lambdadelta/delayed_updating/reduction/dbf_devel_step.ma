include "delayed_updating/reduction/path_dbf_residuals_step.ma".
include "delayed_updating/reduction/dbf_devel_eq.ma".

(* UPDATE *)

lemma dbf_step_conf_local (t0) (t1) (t2) (r1) (r2):
      t0 ϵ 𝐓 → t0 ➡𝐝𝐛𝐟[r1] t1 → t0 ➡𝐝𝐛𝐟[r2] t2 →
      ∃∃t. t1 ⫽➡𝐝𝐛𝐟[r2 /𝐝𝐛𝐟{t0} r1] t & t2 ⫽➡𝐝𝐛𝐟[r1 /𝐝𝐛𝐟{t0} r2] t.
#t0 #t1 #t2 #r1 #r2 #Ht0 #Ht01 #Ht02
elim (eq_path_dec r2 r1) #Hnr12 destruct
[ lapply (dbfs_preterm_mono … Ht0 Ht01 Ht02) -Ht0 -Ht01 -Ht02 #Ht12
  /3 width=3 by dbfd_self, ex2_intro/
| lapply (dbfs_inv_reducuble … Ht01) #Hr1
  lapply (dbfs_inv_reducuble … Ht02) #Hr2
  lapply (path_dbfr_step … Ht0 Ht01 Hr2 r2 ?) -Hr2
  [ /3 width=1 by path_dbfr_neq/ | #H1 ]
  lapply (path_dbfr_step … Ht0 Ht02 Hr1 r1 ?) -Hr1
  [ /3 width=1 by path_dbfr_neq/ | #H2 ]
  elim (dbfs_reducible … H1) -H1 #t3 #Ht13
  elim (dbfs_reducible … H2) -H2 #t4 #Ht24
  cases Ht01 -Ht01 #p1 #b1 #q1 #n1 * #Hr1 #Hb1 #Hq1 #Hn1 #Ht01
  cases Ht02 -Ht02 #p2 #b2 #q2 #n2 * #Hr2 #Hb2 #Hq2 #Hn2 #Ht02
  elim (term_in_slice_dec (⓪p2◖𝗦) r1) #Hp12
  elim (term_in_slice_dec (⓪p2◖𝗦) r2) #Hp21
  [
  |
  |
  | cut (t3 ⇔ t4) [| #Ht34 ]
  ]
]



