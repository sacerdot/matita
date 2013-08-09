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

universe constraint Type[0] < Type[1].

notation "hvbox(a break \to b)"
  right associative with precedence 20
for @{ \forall $_:$a.$b }.

notation "hvbox( * )"
 non associative with precedence 90
 for @{ 'B }.

inductive l: Type[0] ≝ L: l.

inductive g: Type[0] ≝ G: g.

axiom f: l → Prop.

interpretation "b" 'B = L.

interpretation "b" 'B = G.

(* FG: two interpretations of the same notation and with the same description
       override eachother, so the description is not just informative
*)

axiom s: f *.
