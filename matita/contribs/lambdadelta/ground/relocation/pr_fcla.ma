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

include "ground/notation/relations/rfun_c_2.ma".
include "ground/arith/nat_succ.ma".
include "ground/relocation/pr_isi.ma".

(* FINITE COLENGTH ASSIGNMENT FOR PARTIAL RELOCATION MAPS *******************)

(*** fcla *)
inductive pr_fcla: relation2 pr_map nat ā
(*** fcla_isid *)
| pr_fcla_isi (f): šāØfā© ā pr_fcla f (š)
(*** fcla_push *)
| pr_fcla_push (f) (n): pr_fcla f n ā pr_fcla (ā«Æf) n
(*** fcla_next *)
| pr_fcla_next (f) (n): pr_fcla f n ā pr_fcla (āf) (ān)
.

interpretation
  "finite colength assignment (partial relocation maps)"
  'RFunC f n = (pr_fcla f n).

(* Basic inversions *********************************************************)

(*** fcla_inv_px *)
lemma pr_fcla_inv_push (g) (m): šāØgā© ā m ā āf. ā«Æf = g ā šāØfā© ā m.
#g #m * -g -m
[ /3 width=3 by pr_fcla_isi, pr_isi_inv_push/
| #g #m #Hg #f #H >(eq_inv_pr_push_bi ā¦ H) -f //
| #g #m #_ #f #H elim (eq_inv_pr_push_next ā¦ H)
]
qed-.

(*** fcla_inv_nx *)
lemma pr_fcla_inv_next (g) (m): šāØgā© ā m ā āf. āf = g ā āān. šāØfā© ā n & ān = m.
#g #m * -g -m
[ #g #Hg #f #H destruct
  elim (pr_isi_inv_next ā¦ Hg) -Hg //
| #g #m #_ #f #H elim (eq_inv_pr_next_push ā¦ H)
| #g #m #Hg #f #H >(eq_inv_pr_next_bi ā¦  H) -f
  /2 width=3 by ex2_intro/
]
qed-.

(* Advanced inversions ******************************************************)

(*** cla_inv_nn *)
lemma pr_cla_inv_next_succ (g) (m): šāØgā© ā m ā āf,n. āf = g ā ān = m ā šāØfā© ā n.
#g #m #H #f #n #H1 #H2 elim (pr_fcla_inv_next ā¦ H ā¦ H1) -g
#x #Hf #H destruct <(eq_inv_nsucc_bi ā¦ H) -n //
qed-.

(*** cla_inv_np *)
lemma pr_cla_inv_next_zero (g) (m): šāØgā© ā m ā āf. āf = g ā š = m ā ā„.
#g #m #H #f #H1 elim (pr_fcla_inv_next ā¦ H ā¦ H1) -g
#x #_ #H1 #H2 destruct /2 width=2 by eq_inv_zero_nsucc/
qed-.

(*** fcla_inv_xp *)
lemma pr_fcla_inv_zero (g) (m): šāØgā© ā m ā š = m ā šāØgā©.
#g #m #H elim H -g -m /3 width=3 by pr_isi_push/
#g #m #_ #_ #H destruct elim (eq_inv_zero_nsucc ā¦ H)
qed-.

(*** fcla_inv_isid *)
lemma pr_fcla_inv_isi (g) (m): šāØgā© ā m ā šāØgā© ā š = m.
#f #n #H elim H -f -n /3 width=3 by pr_isi_inv_push/
#f #n #_ #_ #H elim (pr_isi_inv_next ā¦ H) -H //
qed-.
