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

include "delayed_updating/syntax/path.ma".
include "delayed_updating/notation/relations/up_down_arrow_epsilon_2.ma".
include "delayed_updating/notation/relations/up_arrow_epsilon_2.ma".

(* TERM *********************************************************************)

definition term: Type[0] ≝ predicate path.

definition term_in_com: relation2 path term ≝
           λp,t. t p.

interpretation
  "belongs to complete (term)"
  'UpDownArrowEpsilon p t = (term_in_com p t).

definition term_in_ini: relation2 path term ≝
           λp,t. ∃q. p;;q ϵ⬦ t.

interpretation
  "belongs to initial (term)"
  'UpArrowEpsilon p t = (term_in_ini p t).

(* Basic constructions ******************************************************)

lemma term_in_com_ini (p) (t):
      p ϵ⬦ t → p ϵ▵ t.
/2 width=2 by ex_intro/
qed.
