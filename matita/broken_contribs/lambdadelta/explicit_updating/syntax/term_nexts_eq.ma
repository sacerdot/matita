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

include "explicit_updating/syntax/term_next_eq.ma".
include "explicit_updating/syntax/term_nexts.ma".

(* ITERATED NEXT FOR TERM ***************************************************)

(* Constructions with term_eq ***********************************************)

lemma term_nexts_eq_repl:
      compatible_3 … (eq …) term_eq term_eq term_nexts.
#n1 #n2 #Hn destruct
@(nat_ind_succ … n2) -n2
/3 width=1 by term_next_eq_repl/
qed.
