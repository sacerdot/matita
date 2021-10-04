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

include "ground/relocation/pr_sle.ma".
include "ground/relocation/pr_sor.ma".

(* RELATIONAL UNION FOR PARTIAL RELOCATION MAPS *****************************)

(* Main inversions with pr_sle **********************************************)

(*** monotonic_sle_sor *)
axiom pr_sor_monotonic_sle:
      ∀f1,g1. f1 ⊆ g1 → ∀f2,g2. f2 ⊆ g2 →
      ∀f. f1 ⋓ f2 ≘ f → ∀g. g1 ⋓ g2 ≘ g → f ⊆ g.
