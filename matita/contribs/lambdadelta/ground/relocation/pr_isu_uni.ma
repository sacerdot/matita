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

include "ground/relocation/pr_isi_uni.ma".
include "ground/relocation/pr_isu.ma".

(* UNIFORMITY CONDITION FOR PARTIAL RELOCATION MAPS *************************)

(* Constructions with pr_uni ************************************************)

(*** isuni_uni *)
lemma pr_isu_uni (n): šāØš®āØnā©ā©.
#n @(nat_ind_succ ā¦ n) -n
/3 width=3 by pr_isu_isi, pr_isu_next/
qed.

(*** uni_inv_isuni *)
lemma pr_isu_eq_repl_back:
      pr_eq_repl_back ā¦ pr_isu.
#f1 #H elim H -f1
[ /3 width=3 by pr_isu_isi, pr_isi_eq_repl_back/
| #f1 #_ #g1 * #IH #f2 #H -g1
  elim (pr_eq_inv_next_sn ā¦ H) -H
  /3 width=3 by pr_isu_next/
]
qed-.

lemma pr_isu_eq_repl_fwd:
      pr_eq_repl_fwd ā¦ pr_isu.
/3 width=3 by pr_isu_eq_repl_back, pr_eq_repl_sym/ qed-.

(* Inversions with pr_uni ***************************************************)

(*** uni_isuni *)
lemma pr_isu_inv_uni (f): šāØfā© ā ān. š®āØnā© ā f.
#f #H elim H -f
[ /3 width=2 by pr_isi_inv_uni, ex_intro/
| #f #_ #g #H * /3 width=6 by pr_eq_next, ex_intro/
]
qed-.
