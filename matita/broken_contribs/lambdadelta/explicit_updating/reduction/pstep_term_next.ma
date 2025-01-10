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
include "explicit_updating/reduction/pstep_term.ma".

(* P-REDUCTION FOR TERM *****************************************************)

(* Constructions with term_next *********************************************)

lemma pstep_term_next_bi (R2) (t1) (t2):
      t1 ⫽➡[R2] t2 → ↑t1 ⫽➡[R2] ↑t2.
/2 width=1 by pstep_term_lift/
qed.
