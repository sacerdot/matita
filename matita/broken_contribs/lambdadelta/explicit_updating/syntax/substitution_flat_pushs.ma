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
include "explicit_updating/syntax/substitution_flat_push.ma".

(* FLATTENING FOR SUBSTITUTION **********************************************)

(* Constructions with subst_pushs *******************************************)

lemma subst_flat_pushs (n) (S):
      (⫯*[n]♭S) ≐ ♭⫯*[n]S.
#n @(nat_ind_succ … n) -n //
/3 width=5 by subst_push_eq_repl, subst_eq_repl/
qed.
