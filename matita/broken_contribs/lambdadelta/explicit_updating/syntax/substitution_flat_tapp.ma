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

include "explicit_updating/syntax/substitution_tapp_eq.ma".
include "explicit_updating/syntax/substitution_flat_push.ma".

(* FLATTENING FOR SUBSTITUTION **********************************************)

(* Constructions with subst_tapp ********************************************)

lemma subst_flat_tapp (t:𝕋) (S):
      (♭S)＠⧣❨♭t❩ ≐ ♭(S＠⧣❨t❩).
#t elim t -t //
[ /4 width=5 by subst_tapp_eq_repl, term_eq_trans, term_eq_abst/
| /2 width=1 by term_eq_appl/
]
qed.
