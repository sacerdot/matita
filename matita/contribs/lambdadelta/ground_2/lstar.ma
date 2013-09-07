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

include "arithmetics/lstar.ma".

(* PROPERTIES OF NAT-LABELED REFLEXIVE AND TRANSITIVE CLOSURE ***************)

definition llstar: ∀A:Type[0]. ∀B. (A→relation B) → nat → (A→relation B) ≝
                   λA,B,R,l,a. lstar … (R a) l.
