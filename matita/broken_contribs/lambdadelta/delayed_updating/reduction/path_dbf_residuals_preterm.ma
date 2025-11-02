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

lemma path_dbfr_side_eq (t) (x) (r) (p) (b) (q) (n):
      t ϵ 𝐓 → r ϵ 𝐑❨t,p,b,q,n❩ → x ϵ 𝐏 →
      let s ≝ (⓪p)◖𝗦●(⓪x) in
      ❴s,r●⓪x❵ ⇔ (s /𝐝𝐛𝐟{t} r).
/3 width=7 by path_dbfr_side_ge, path_dbfr_side_le, conj/
qed.
