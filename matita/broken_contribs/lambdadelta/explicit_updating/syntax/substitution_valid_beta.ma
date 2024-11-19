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

include "explicit_updating/syntax/substitution_beta.ma".
include "explicit_updating/syntax/substitution_valid.ma".

(* VALIDITY FOR SUBSTITUTION ************************************************)

(* Constructions with subst_beta ********************************************)

lemma substitution_valid_beta (b) (t):
      b ⊢ t → b ⊢ 𝐬❨t❩.
#b #t #Ht *
/2 width=1 by term_valid_lref/
qed.

(* Inversions with subst_beta ***********************************************)

lemma substitution_valid_inv_beta (b) (t):
      b ⊢ 𝐬❨t❩ → b ⊢ t.
//
qed-.
