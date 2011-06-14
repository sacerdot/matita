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

include "lambda-delta/substitution/lift_defs.ma".

(* RELOCATION ***************************************************************)

(* the functional properties **************************************************)

axiom lift_total: ∀d,e,T1. ∃T2. ↑[d,e] T1 ≡ T2.

axiom lift_mono:  ∀d,e,T,U1. ↑[d,e] T ≡ U1 → ∀U2. ↑[d,e] T ≡ U2 → U1 = U2.

axiom lift_inj:  ∀d,e,T1,U. ↑[d,e] T1 ≡ U → ∀T2. ↑[d,e] T2 ≡ U → T1 = T2.
