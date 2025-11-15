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

include "delayed_updating/reduction/preterm_reducible.ma".
include "delayed_updating/reduction/path_dbf_residuals_le.ma".

(* RESIDUALS OF A DBF-REDEX POINTER *****************************************)

(* Destructions with preterm and subset_le **********************************)

lemma path_dbfr_neq_ge (t) (s) (r) (p) (b) (q) (n):
      t ϵ 𝐓 → r ϵ 𝐑❨t,p,b,q,n❩ → ⓪s = s → s ⧸ϵ ⓪▵↑(p◖𝗦) →
      (s /𝐝𝐛𝐟{t} r) ⊆ ❴s❵.
#t #s #r #p #b #q #n #Ht #Hr * #Hs #x * *
[ #_ #H0 destruct //
| #p0 #b0 #q0 #q1 #n0 #H0r #Hq1 >path_clear_S_dx #H0s #H0 destruct
  elim (eq_inv_path_append_clear … H0s) -H0s #x #y #Hx #Hy #H0 destruct
  lapply (subset_ol_i ???? Hr H0r) -Hr -H0r #H0
  elim (ol_des_xprc_bi … Ht H0) -Ht -H0 #H1 #H2 #H3 #H4 destruct
  elim Hs -Hs <path_clear_append <Hx -x >path_clear_append
  /3 width=1 by in_comp_term_clear, term_in_comp_root/
]
qed.

lemma path_dbfr_side_ge (t) (x) (r) (p) (b) (q) (n):
      t ϵ 𝐓 → r ϵ 𝐑❨t,p,b,q,n❩ →
      let s ≝ (⓪p)◖𝗦●(⓪x) in
      (s /𝐝𝐛𝐟{t} r) ⊆ ❴s,r●⓪x❵.
#t #x #r #p #b #q #n #Ht #Hr #y * *
[ #_ #H0 destruct //
| #p0 #b0 #q0 #x0 #n0 #Hr0 #_ #H0 #H1 destruct
  lapply (subset_ol_i ???? Hr0 … Hr) -Hr0 -Hr #H1
  elim (ol_des_xprc_bi … Ht H1) -t #H1 #_ #_ #_ destruct -b -b0 -q -q0 -n -n0
  lapply (eq_inv_list_append_dx_bi … H0) -H0 #H0 destruct //
]
qed.

(* Constructions with preterm and subset_eq *********************************)

lemma path_dbfr_neq_eq (t) (s) (r) (p) (b) (q) (n):
      t ϵ 𝐓 → r ϵ 𝐑❨t,p,b,q,n❩ → s ⧸= r → ⓪s = s → s ⧸ϵ ⓪▵↑(p◖𝗦) →
      ❴s❵ ⇔ (s /𝐝𝐛𝐟{t} r).
/3 width=10 by path_dbfr_neq_ge, path_dbfr_neq_le, conj/
qed.

lemma path_dbfr_side (t) (x) (s) (r) (p) (b) (q) (n):
      t ϵ 𝐓 → r ϵ 𝐑❨t,p,b,q,n❩ → x ϵ 𝐏 → s = (⓪p)◖𝗦●(⓪x) →
      ❴s,r●⓪x❵ ⇔ (s /𝐝𝐛𝐟{t} r).
/3 width=7 by path_dbfr_side_ge, path_dbfr_side_le, conj/
qed.

lemma path_dbfr_side_sx (t1) (t2) (r1) (r2) (p1) (p2) (b1) (b2) (q1) (q2) (n2) (n1) (x):
      t1 ϵ 𝐓 →
      r1 ϵ 𝐑❨t1,p1,b1,q1,n1❩ → r2 ϵ 𝐑❨t2,p2,b2,q2,n2❩ →
      r2 ⧸ϵ ⓪▵↑(p1◖𝗦) → ⓪(p2◖𝗦)●⓪x = r1 →
      ❴r2●⓪x❵ ⇔ (r2●⓪x) /𝐝𝐛𝐟{t1} r1.
#t1 #t2 #r1 #r2 #p1 #p2 #b1 #b2 #q1 #q2 #n1 #n2 #x #Ht #Hr1 #Hr2 #Hnr2 #H0
@(path_dbfr_neq_eq … Hr1)
[ //
| <H0 <(xprc_des_r … Hr2) <path_clear_beta <path_clear_S_dx
  /3 width=7 by path_neq_p_beta, sym_eq/
| <(xprc_des_clear … Hr2) in ⊢ (???%); //
| <(xprc_des_clear … Hr2) in Hnr2; >path_clear_append #Hnr2
  /3 width=2 by term_ol_clear_slice_bi_des_append_sx_dx/
]
qed.
