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

include "explicit_updating/syntax/substitution_tapp.ma".
include "explicit_updating/syntax/substitution_valid_after.ma".
include "explicit_updating/syntax/substitution_valid_push.ma".

(* VALIDITY FOR SUBSTITUTION ************************************************)

(* Constructions with subst_tapp ********************************************)

lemma subst_valid_tapp (b) (t):
      b ⊢ t → ∀S. b ⊢ S → b ⊢ S＠⧣❨t❩.
#b #t #Ht elim Ht -Ht
[ //
| /4 width=1 by subst_valid_push, term_valid_abst/
| /3 width=1 by term_valid_appl/
| /3 width=1 by subst_valid_after/
| /4 width=1 by subst_valid_push, term_valid_beta/
]
qed.
