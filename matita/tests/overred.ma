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



include "logic/equality.ma".

axiom T1 : Type.
axiom X : Type.
axiom x : X.
definition T2 : Type := T1.
definition T3 : Type := T2.
axiom t3 : T3.
axiom c : T2 -> X -> X.

coercion cic:/matita/tests/overred/c.con 1.

axiom daemon : c t3 x = x. 

theorem find_a_coercion_from_T2_for_a_term_in_T3 : (* c *) t3 x = x.
apply daemon.
qed.
