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

include "ground/arith/nat_plus.ma".
(* * it should not depend on pr_isi *)
include "ground/relocation/pr_isi_uni.ma".
include "ground/relocation/pr_after_isi.ma".

(* RELATIONAL COMPOSITION FOR PARTIAL RELOCATION MAPS ***********************)

(* Constructions with pr_uni ************************************************)

(*** after_uni *)
lemma pr_after_uni (h1) (h2): ð®â¨h1â© â ð®â¨h2â© â ð®â¨h2+h1â©.
#h1 @(nat_ind_succ â¦ h1) -h1
/3 width=5 by pr_after_isi_sn, pr_after_next, eq_f/
qed.

(*** after_uni_sn_pushs *)
lemma pr_after_uni_sn_pushs (h):
      âf. ð®â¨hâ© â f â â*[h]f.
#h @(nat_ind_succ â¦ h) -h
/2 width=5 by pr_after_isi_sn, pr_after_next/
qed.

lemma pr_after_uni_isi_next (h1):
      âf2. ðâ¨f2â© â ð®â¨h1â© â âf2 â âð®â¨h1â©.
#h1 @(nat_ind_succ â¦ h1) -h1
/5 width=7 by pr_after_isi_dx, pr_after_eq_repl_back_sn, pr_after_next, pr_after_push, pr_isi_inv_eq_push/
qed.

lemma pr_after_uni_next_sn (h2):
      âf1,f. âð®â¨h2â© â f1 â f â ð®â¨h2â© â âf1 â f.
#h2 @(nat_ind_succ â¦ h2) -h2
[ #f1 #f #Hf
  elim (pr_after_inv_next_sn â¦ Hf) -Hf [2,3: // ] #g #Hg #H0 destruct
  /4 width=7 by pr_after_isi_inv_sn, pr_after_isi_sn, pr_after_eq_repl_back, pr_eq_next/
| #h2 #IH #f1 #f #Hf
  elim (pr_after_inv_next_sn â¦ Hf) -Hf [2,3: // ] #g #Hg #H0 destruct
  /3 width=5 by pr_after_next/
]
qed.
