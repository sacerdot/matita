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

include "explicit_updating/computation/xsteps.ma".

(* X-COMPUTATION ************************************************************)

axiom xstep_strip (R) (t0) (t1) (t2):
      t0 ➡[R] t1 → t0 ➡*[R] t2 →
      ∃∃t. t1 ➡*[R] t & t2 ➡*[R] t.

theorem xstep_confluence (R) (t0) (t1) (t2):
        replace_2 … term_eq term_eq R →
        t0 ➡*[R] t1 → t0 ➡*[R] t2 →
        ∃∃t. t1 ➡*[R] t & t2 ➡*[R] t.
#R #t0 #t1 #t2 #HR #Ht01 #Ht02 elim Ht01 -t1
[ /3 width=7 by xsteps_eq_repl, xsteps_refl, ex2_intro/
| #t3 #t1 #_ #Ht31 * #t4 #Ht34 #Ht24
  elim (xstep_strip … Ht31 Ht34) -t3 #t3 #Ht13 #Ht43
  /3 width=5 by xsteps_trans, ex2_intro/
]
qed-.
