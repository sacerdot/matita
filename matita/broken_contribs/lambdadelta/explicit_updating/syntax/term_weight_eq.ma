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
include "explicit_updating/syntax/term_weight.ma".

(* WEIGHT FOR TERM **********************************************************)

(* Constructions with term_eq ***********************************************)

lemma term_weight_eq_repl:
      compatible_2_fwd … term_eq (eq …) term_weight.
#t1 #t2 #Ht12 elim Ht12 -t1 -t2 //
qed.
