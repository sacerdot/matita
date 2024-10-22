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

include "explicit_updating/syntax/term_eq.ma".
include "explicit_updating/syntax/term_flat.ma".

(* FLATTENING FOR TERM ******************************************************)

(* Constructions with term_eq ***********************************************)

lemma term_flat_eq_repl:
      compatible_2_fwd … term_eq term_eq term_flat.
#t1 #t2 #Ht elim Ht -t1 -t2
/2 width=1 by term_eq_abst, term_eq_appl, term_eq_lift/
qed.
