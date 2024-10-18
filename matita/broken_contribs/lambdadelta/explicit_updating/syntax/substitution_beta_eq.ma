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

include "explicit_updating/syntax/substitution_eq.ma".
include "explicit_updating/syntax/substitution_beta.ma".

(* SUBSTITUTION FOR β-REDUCTION *********************************************)

(* Constructions with extensional equivalence for substitution **************)

lemma subst_beta_eq_repl:
      compatible_2_fwd … term_eq subst_eq subst_beta.
#t1 #t2 #Ht * //
qed.
