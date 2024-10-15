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

include "ground/relocation/fb/fbr_uni.ma".
include "explicit_updating/syntax/term.ma".

(* NEXT FOR TERM ************************************************************)

definition term_next (t): 𝕋 ≝
           ϕ(𝐮❨⁤𝟏❩).t
.

interpretation
  "next (term)"
  'UpArrow t = (term_next t).

(* Basic constructions ******************************************************)

lemma term_next_unfold (t):
      ϕ(𝐮❨⁤𝟏❩).t = ↑t.
//
qed.
