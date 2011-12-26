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

include "Basic_2/substitution/lift_vector.ma".

(* GENERIC RELOCATION *******************************************************)

inductive lifts: list2 nat nat → relation term ≝
| lifts_nil : ∀T. lifts ⟠ T T
| lifts_cons: ∀T1,T,T2,des,d,e.
              ⇑[d,e] T1 ≡ T → lifts des T T2 → lifts ({d, e} :: des) T1 T2
.

interpretation "generic relocation" 'RLift des T1 T2 = (lifts des T1 T2).
