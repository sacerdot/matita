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

include "explicit_updating/syntax/substitution_push_eq.ma".
include "explicit_updating/syntax/substitution_pushs.ma".

(* ITERATED PUSH FOR SUBSTITUTION *******************************************)

(* Constructions with extensional equivalence for substitution **************)

lemma subst_pushs_eq_repl:
      compatible_3 … (eq …) subst_eq subst_eq subst_pushs.
#n1 #n2 #Hn destruct
@(nat_ind_succ … n2) -n2
/3 width=1 by subst_push_eq_repl/
qed.
