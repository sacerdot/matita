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

include "delayed_updating/reduction/prototerm_reducible_preterm.ma".
include "delayed_updating/reduction/path_dbf_residuals.ma".

(* RESIDUALS OF A DBF-REDEX POINTER *****************************************)

(* Constructions with prototerm *********************************************)

lemma path_dbfr_inv_neq_le (t) (s) (r) (p) (b) (q) (n):
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
