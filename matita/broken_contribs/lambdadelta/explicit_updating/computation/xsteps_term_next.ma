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

include "explicit_updating/syntax/term_next.ma".
include "explicit_updating/computation/xsteps_term.ma".

(* X-COMPUTATION FOR TERM ***************************************************)

(* Constructions with term_next *********************************************)

lemma xsteps_term_next_bi (R) (t1) (t2):
      t1 ➡*[R] t2 → ↑t1 ➡*[R] ↑t2.
/2 width=1 by xsteps_term_lift_bi/
qed.
