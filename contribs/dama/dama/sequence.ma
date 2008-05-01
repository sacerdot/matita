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

include "excess.ma".

definition sequence := λO:Type.nat → O.

definition fun_of_sequence: ∀O:Type.sequence O → nat → O ≝ λO.λx:sequence O.x.

coercion cic:/matita/sequence/fun_of_sequence.con 1.
