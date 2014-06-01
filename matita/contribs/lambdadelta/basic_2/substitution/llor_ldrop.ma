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

include "basic_2/substitution/frees_lift.ma".
include "basic_2/substitution/llor.ma".

(* POINTWISE UNION FOR LOCAL ENVIRONMENTS ***********************************)

(* Advanced properties ******************************************************)

axiom llor_total: ∀L1,L2,T. |L1| ≤ |L2| → ∃L. L1 ⩖[T] L2 ≡ L.
