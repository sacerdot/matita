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

include "explicit_updating/syntax/substitution_push.ma".
include "explicit_updating/computation/xsteps_term_next.ma".
include "explicit_updating/computation/xsteps_substitution.ma".

(* X-COMPUTATION FOR SUBSTITUTION *******************************************)

(* Constructions with subst_push ********************************************)

lemma xsteps_subst_push_bi (R) (S1) (S2):
      S1 ➡*[R] S2 → ⫯S1 ➡*[R] ⫯S2.
#R #S1 #S2 #HS12 *
/2 width=3 by xsteps_term_next_bi, xsteps_term_refl/
qed.
