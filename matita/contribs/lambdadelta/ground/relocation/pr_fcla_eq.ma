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

include "ground/relocation/pr_isi_eq.ma".
include "ground/relocation/pr_fcla.ma".

(* FINITE COLENGTH ASSIGNMENT FOR PARTIAL RELOCATION MAPS *******************)

(* Constructions with pr_eq *************************************************)

(*** fcla_eq_repl_back *)
lemma pr_fcla_eq_repl_back (n):
      pr_eq_repl_back … (λf. 𝐂❨f❩ ≘ n).
#n #f1 #H elim H -f1 -n /3 width=3 by pr_fcla_isi, pr_isi_eq_repl_back/
#f1 #n #_ #IH #g2 #H [ elim (pr_eq_inv_push_sn … H) | elim (pr_eq_inv_next_sn … H) ] -H
/3 width=3 by pr_fcla_push, pr_fcla_next/
qed-.

(*** fcla_eq_repl_fwd *)
lemma fcla_eq_repl_fwd (n):
      pr_eq_repl_fwd … (λf. 𝐂❨f❩ ≘ n).
#n @pr_eq_repl_sym /2 width=3 by pr_fcla_eq_repl_back/
qed-.
