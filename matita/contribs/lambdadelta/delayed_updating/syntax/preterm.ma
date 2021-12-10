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

(* PRETERM ******************************************************************)

definition preterm: Type[0] ≝ predicate path.

definition preterm_in_comp: relation2 path preterm ≝
           λp,t. t p.

interpretation
  "belongs to complete (preterm)"
  'UpDownArrowEpsilon p t = (preterm_in_comp p t).

definition preterm_in_root: relation2 path preterm ≝
           λp,t. ∃q. p;;q ϵ⬦ t.

interpretation
  "belongs to root (preterm)"
  'UpArrowEpsilon p t = (preterm_in_root p t).

(* Basic constructions ******************************************************)

lemma preterm_in_comp_root (p) (t):
      p ϵ⬦ t → p ϵ▵ t.
/2 width=2 by ex_intro/
qed.
