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

(* notations ****************************************************************)

notation "hvbox(a break \to b)"
  right associative with precedence 20
for @{ \forall $_:$a.$b }.

notation "hvbox( T . break ⓑ { term 46 I } break term 48 T1 )"
 non associative with precedence 47
 for @{ 'DxBind2 $T $I $T1 }.

(* definitions **************************************************************)

inductive lenv: Type[0] ≝
| LAtom: lenv
| LPair: lenv → lenv → lenv → lenv
.

inductive genv: Type[0] ≝
| GAtom: genv
| GPair: genv → genv → genv → genv
.

axiom fw: genv → lenv → Prop.

(* interpretations **********************************************************)

interpretation "environment binding construction (binary)"
   'DxBind2 L I T = (LPair L I T).

interpretation "environment binding construction (binary)"
   'DxBind2 G I T = (GPair G I T).

(* statements ***************************************************************)

axiom fw_shift: ∀I,G,K,V. fw G (K.ⓑ{I}V).
