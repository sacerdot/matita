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

include "ground/subsets/subset_eq.ma".
include "delayed_updating/reduction/preterm_reducible.ma".
include "delayed_updating/reduction/path_dbf_residuals_le.ma".

(* RESIDUALS OF A DBF-REDEX POINTER *****************************************)

(* Destructions with preterm and subset_le **********************************)

lemma path_dbfr_des_neq_le (t) (s) (r) (p) (b) (q) (n):
      t ϵ 𝐓 → r ϵ 𝐑❨t,p,b,q,n❩ → s ⧸ϵ ↑(⓪p◖𝗦) →
      (s /𝐝𝐛𝐟{t} r) ⊆ ❴s❵.
#t #s #r #p #b #q #n #Ht #Hr #Hs #x * *
[ #_ #H0 destruct //
| #p0 #b0 #q0 #q1 #n0 #H0r #H1 #H2 destruct
  lapply (subset_ol_i ???? Hr H0r) -Hr -H0r #H0
  elim (xprc_des_ol … Ht H0) -H0 #H1 #H2 #H3 #H4 destruct
  elim Hs -Hs //
]
qed.

(* Constructions with preterm and subset_eq *********************************)

lemma path_dbfr_neq_eq (t) (s) (r) (p) (b) (q) (n):
      t ϵ 𝐓 → r ϵ 𝐑❨t,p,b,q,n❩ → s ⧸= r → s ⧸ϵ ↑(⓪p◖𝗦) →
      ❴s❵ ⇔ (s /𝐝𝐛𝐟{t} r).
/3 width=10 by path_dbfr_des_neq_le, path_dbfr_neq_le, conj/
qed.
