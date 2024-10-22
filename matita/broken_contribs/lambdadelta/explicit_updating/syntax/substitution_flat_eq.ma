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
include "explicit_updating/syntax/term_flat_eq.ma".
include "explicit_updating/syntax/substitution_flat.ma".

(* FLATTENING FOR SUBSTITUTION **********************************************)

(* Constructions with subst_eq **********************************************)

lemma subst_flat_eq_repl:
      compatible_2_fwd … subst_eq subst_eq subst_flat.
#S1 #S2 #HS #p
/3 width=1 by term_flat_eq_repl, subst_dapp_eq_repl/
qed.
