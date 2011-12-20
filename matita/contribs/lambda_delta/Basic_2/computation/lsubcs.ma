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

include "Basic_2/computation/lsubc.ma".
include "Basic_2/computation/csn.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR STRONG NORMALIZATION ********************)

definition lsubcs: relation lenv ≝ lsubc csn.

interpretation
  "local environment refinement (strong normalization)"
  'CrSubEq L1 L2 = (lsubcs L1 L2).

(* Basic properties *********************************************************)

lemma lsubcs_refl: ∀L. L ⊑ L.
// qed.

(* Basic inversion lemmas ***************************************************)
