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
include "explicit_updating/computation/xsteps_substitution_push.ma".

(* X-COMPUTATION FOR SUBSTITUTION *******************************************)

(* Constructions with subst_tapp ********************************************)

lemma xsteps_subst_tapp_dx_bi (R) (t:𝕋) (S1) (S2):
      S1 ➡*[R] S2 → S1＠⧣❨t❩ ➡*[R] S2＠⧣❨t❩.
#R #t elim t -t
[ //
| /4 width=1 by xsteps_subst_push_bi, xsteps_term_abst_bi/
| /3 width=1 by xsteps_term_appl_bi/
| /2 width=1 by/
]
qed.
