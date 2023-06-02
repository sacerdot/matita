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

include "ground/relocation/trz_eq.ma".
include "ground/notation/functions/compose_2.ma".

(* COMPOSITION FOR TOTAL RELOCATION MAPS WITH INTEGERS **********************)

definition trz_after (f2:trz_map) (f1:trz_map): trz_map ≝ mk_trz_map ….
[ @(trz_staff f2 ∘ trz_staff f1)
| @compose_injective_2_fwd //
]
defined.

interpretation
  "composition (total relocation maps with integers)"
  'Compose f2 f1 = (trz_after f2 f1).

(* Basic constructions ******************************************************)

lemma trz_after_unfold (f1) (f2) (z):
      f2＠⧣❨f1＠⧣❨z❩❩ = (f2•f1)＠⧣❨z❩.
// qed.

lemma trz_after_eq_repl:
      compatible_3 … trz_eq trz_eq trz_eq trz_after.
// qed.

(* Main constructions *******************************************************)

theorem trz_after_assoc (f3) (f2) (f1):
        (f3•f2)•f1 ≐ f3•(f2•f1).
// qed.
