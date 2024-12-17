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
include "explicit_updating/syntax/substitution_after_eq.ma".
include "explicit_updating/syntax/substitution_tapp.ma".

(* TERM APPLICATION FOR SUBSTITUTION ****************************************)

(* Constructions with subst_eq **********************************************)

lemma subst_tapp_eq_repl:
      compatible_3 … subst_eq term_eq term_eq subst_tapp.
#S1 #S2 #HS #t1 #t2 #Ht
generalize in match HS; -HS
generalize in match S2; -S2
generalize in match S1; -S1
elim Ht -t1 -t2
[ #S1 #S2 #HS //
| #b #t1 #t2 #_ #IH #S1 #S2 #HS
  /4 width=1 by term_eq_abst, subst_push_eq_repl/
| #v1 #v2 #t1 #t2 #_ #_ #IHv #IHt #S1 #S2 #HS
  /3 width=1 by term_eq_appl/
| #f1 #f2 #t1 #t2 #Hf #_ #IH #S1 #S2 #HS
  /4 width=1 by term_eq_lift, subst_after_eq_repl/
]
qed.
