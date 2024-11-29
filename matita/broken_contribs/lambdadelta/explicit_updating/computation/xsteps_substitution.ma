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

include "explicit_updating/syntax/substitution.ma".
include "explicit_updating/computation/xsteps_term.ma".

(* X-COMPUTATION FOR SUBSTITUTION *******************************************)

definition xsteps_subst (R): relation2 (𝕊) (𝕊) ≝
           λS1,S2. ∀p. S1＠⧣❨p❩ ➡*[R] S2＠⧣❨p❩.

interpretation
  "x-computation (substitution)"
  'BlackRightArrowStar S1 R S2 = (xsteps_subst R S1 S2).
