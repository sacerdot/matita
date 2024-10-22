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

include "explicit_updating/syntax/substitution_pushs_eq.ma".
include "explicit_updating/syntax/substitution_flat_pushs.ma".
include "explicit_updating/syntax/substitution_flat_tapp.ma".
include "explicit_updating/syntax/substitution_flat_beta.ma".
include "explicit_updating/syntax/beta.ma".

(* β-SUBSTITUTION FOR TERM **************************************************)

(* Constructions with term_flat *********************************************)

lemma beta_flat (n) (v) (t):
      ⬕[n←♭v]♭t ≐ ♭⬕[n←v]t.
#n #v #t
<beta_unfold <beta_unfold
@(term_eq_trans … (subst_flat_tapp …))
@subst_tapp_eq_repl //
@(subst_eq_trans … (subst_flat_pushs …))
/2 width=1 by subst_pushs_eq_repl/
qed.
