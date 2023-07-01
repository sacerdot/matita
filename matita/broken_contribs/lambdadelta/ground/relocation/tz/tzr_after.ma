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

include "ground/relocation/tz/tzr_map.ma".
include "ground/notation/functions/compose_2.ma".

(* COMPOSITION FOR TOTAL RELOCATION MAPS WITH INTEGERS **********************)

definition tzr_after (f2:tzr_map) (f1:tzr_map): tzr_map ≝ mk_tzr_map ….
[ @(tzr_staff f2 ∘ tzr_staff f1)
| @compose_injective_2_fwd //
]
defined.

interpretation
  "composition (total relocation maps with integers)"
  'Compose f2 f1 = (tzr_after f2 f1).

(* Basic constructions ******************************************************)

lemma tzr_after_dapp (f1) (f2) (z):
      f2＠⧣❨f1＠⧣❨z❩❩ = (f2•f1)＠⧣❨z❩.
// qed.

lemma tzr_after_eq_repl:
      compatible_3 … tzr_eq tzr_eq tzr_eq (λf2,f1.f2•f1).
// qed.

(* Main constructions *******************************************************)

theorem tzr_after_assoc (f3) (f2) (f1):
        (f3•f2)•f1 ≐ f3•(f2•f1).
// qed.
